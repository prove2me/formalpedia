-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_theorem_1
-- name    : DynEdgeColorLLL.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:01.016624+00:00
-- url     : https://prove2.me/theorems/6e845d55-3eed-457c-b22b-8070e8233f95
-- title:
--   Theorem 1 — proper $(1+\epsilon)\Delta$ edge colouring in $\mathrm{poly}(1/\epsilon)$ worst-case expected update time for every $\Delta\ge\tilde O(1/\epsilon^2)$
-- statement:
--   There are absolute constants $a$, $C_1,k_1$ and $C_2,k_2$ such that the following holds. For every $0<\epsilon<1$ there are a threshold
--   $$\Delta_\epsilon\le C_1\,\epsilon^{-2}\bigl(1+\ln(1/\epsilon)\bigr)^{k_1}$$
--   and a randomized dynamic program $P$ on the word RAM with word size $a\lceil\log_2(n+1)\rceil$. Take any $n\ge2$, any fixed degree bound $\Delta\ge\Delta_\epsilon$, and any sequence $\sigma$ of edge insertions and deletions on $n$ vertices, starting from the empty graph, that keeps the graph simple with maximum degree at most $\Delta$ and is fixed before the random words are drawn (an oblivious adversary). The program receives $n$ and $\min(\Delta,n)$ before the first update. Then:
--   1. almost surely, after preprocessing and after every update, the program reaches a completed state, and the edge colouring it has written is a proper edge colouring of the current graph with colours in $\{1,\dots,\lfloor(1+\epsilon)\Delta\rfloor\}$;
--   2. for every single update $t$, the number of steps it takes is a measurable random variable with
--   $$\mathbb E\bigl[\text{steps of update }t\bigr]\le C_2\,\epsilon^{-k_2}.$$
--
--   This is the paper's main result. It answers the open question of Bhattacharya, Costa, Panski and Solomon [BCPS24], whose constant-time algorithm needs $\Delta\ge(\log n/\epsilon^4)^{\Theta(\log(1/\epsilon)/\epsilon)}$: here the degree threshold depends on $\epsilon$ only, and the update time is independent of $n$ and $\Delta$. The bound is on the expected cost of each update, not an amortized average.
--
--   **Formalization Note.** The machine is the published `DynBrooks_Machine` and the update protocol is `DynColorWC_Main_Model`. The colouring is what the machine writes: output triples $u,v,q$ ("edge $\{u,v\}$ gets colour $q$"), applied in order to the all-$0$ labelling. Because $0$ is outside the palette, every present edge must have been written. A run that never completes has infinite step count, so the time bound also forces completion of preprocessing and of every earlier update almost surely.
--
--   Differences from the source:
--   - reading: a threshold Δ_ε = Õ(1/ε²) → a natural number Δ_ε with Δ_ε ≤ C₁(1/ε)²(1 + ln(1/ε))^{k₁}, C₁, k₁ absolute; the statement then holds for every Δ ≥ Δ_ε; reason: Õ hides factors polylogarithmic in 1/ε (PDF p. 3); Δ_ε has no closed form in the paper, so it is existential with this upper bound
--   - reading: poly(1/ε) worst-case expected time per update → E[steps of update t] ≤ C₂(1/ε)^{k₂} for every update index t, with C₂, k₂ absolute and chosen before ε; reason: poly(1/ε) with constants uniform in ε; worst-case expected means a bound for every single update, not an amortized one (PDF p. 3)
--   - encoding: at most (1+ε)Δ colours → colours in {1, …, ⌊(1+ε)Δ⌋}; reason: every colour in {1, …, ⌊(1+ε)Δ⌋} gives at most (1+ε)Δ colours, and the paper's colourings use fixed palettes
--   - reading: a randomized dynamic algorithm on a word RAM with O(log n)-bit words and unit-cost random words → one DynBrooks.Program on the published word RAM with word size a·⌈log₂(n+1)⌉ (a absolute), fixed before the vertex count and the degree bound; preprocessing receives the words n and min(Δ, n); reason: the paper names this model (PDF pp. 16, 37–38) and the program is chosen before n and Δ; min(Δ, n) loses nothing because degrees are at most n − 1
--   - reading: edge insertions and deletions in a simple graph of maximum degree at most Δ, against an oblivious adversary → every n ≥ 2 and every update list σ legal from the empty graph (DynColorWC.Main.IsLegalSeq Δ σ), quantified before the coin tape; reason: σ fixed before the coins is the oblivious adversary; an initial graph is built by insertions; for n ≤ 1 there are no edges
--   - reading: the algorithm maintains the colouring → almost surely, for every t ≤ |σ|, the completed state after t updates is reached and the colouring written by the machine (output triples u, v, q from the all-0 labelling) is proper for the current graph; reason: the LLL maintenance terminates only almost surely (PDF p. 13); the colouring must be the one the machine writes
--   - encoding: expected time of each update → for every update index t < |σ|, the step count updateTime of update t is measurable and its lower Lebesgue integral against the coin measure is bounded; reason: measurability makes the integral the expectation; a run that never completes has step count ⊤, so the bound also forces completion of every earlier update and of preprocessing almost surely
--   - reading: no statement about preprocessing time → preprocessing time is not bounded; reason: the theorem bounds only the update time; the paper computes its parameters in O(log Δ) time before the first update (PDF p. 37)
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Theorem 1, printed p. 1 (PDF p. 3), with the context sentences on the same page ("the theorem bounds the expected cost of each update", "the oblivious adversary … fixes the update sequence", "The Õ notation hides factors polylogarithmic in 1/ε")

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model
import Definitions.Def_DynEdgeColorLLL_Main_EdgeReadout
open MeasureTheory
open scoped ENNReal

namespace DynEdgeColorLLL.Main

/-- Theorem 1 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 1, PDF p. 3). For every
`0 < ε < 1` there are a threshold `Δ_ε = Õ(1/ε²)` and a randomized dynamic program such that, for
every fixed degree bound `Δ ≥ Δ_ε`, every `n ≥ 2` and every legal update sequence `σ` fixed in
advance (oblivious adversary), almost surely every completed state is reached and the written edge
colouring is proper with colours in `{1, …, ⌊(1+ε)Δ⌋}`, and every update takes `poly(1/ε)`
expected steps. The constants `a, k₁, k₂, C₁, C₂` are absolute. -/
theorem theorem_1 :
    ∃ (a k₁ k₂ : ℕ) (C₁ C₂ : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (Δε : ℕ) (P : DynBrooks.Program),
        (Δε : ℝ) ≤ C₁ * (1 / ε) ^ 2 * (1 + Real.log (1 / ε)) ^ k₁ ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ (Δ : ℕ), Δε ≤ Δ →
        ∀ σ : List (DynBrooks.Update n), DynColorWC.Main.IsLegalSeq Δ σ →
          (∀ᵐ ω ∂(DynBrooks.coinMeasure (DynColorWC.Main.wordSize a n)),
            ∀ t ≤ σ.length,
              (DynColorWC.Main.stateAt P ω [n, min Δ n] σ t).isSome ∧
              IsProperEdgeColoring ⌊(1 + ε) * (Δ : ℝ)⌋₊ (DynColorWC.Main.graphAt σ t)
                (edgeColorAt P ω [n, min Δ n] σ t)) ∧
          ∀ t < σ.length,
            Measurable (fun ω : ℕ → BitVec (DynColorWC.Main.wordSize a n) =>
              ((DynColorWC.Main.updateTime P ω [n, min Δ n] σ t : ℕ∞) : ℝ≥0∞)) ∧
            ∫⁻ ω, ((DynColorWC.Main.updateTime P ω [n, min Δ n] σ t : ℕ∞) : ℝ≥0∞)
                ∂(DynBrooks.coinMeasure (DynColorWC.Main.wordSize a n)) ≤
              ENNReal.ofReal (C₂ * (1 / ε) ^ k₂) := by sorry

end DynEdgeColorLLL.Main
