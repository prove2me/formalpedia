-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_theorem_3
-- name    : DynEdgeColorLLL.Main.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:48.08558+00:00
-- url     : https://prove2.me/theorems/f7bba421-1d73-4e53-9bc8-567e68db4e39
-- title:
--   Theorem 3 — dynamic $(1+\epsilon)\Delta$ edge colouring in $\mathrm{poly}(\Delta)$ expected update time
-- statement:
--   For every $0<\epsilon<1$ there are a threshold $\Delta_\epsilon=\tilde O(1/\epsilon^2)$ and a randomized dynamic program with the following guarantee, for every $n\ge2$, every degree bound $\Delta\ge\Delta_\epsilon$ and every sequence of edge insertions and deletions fixed in advance that keeps the graph simple with maximum degree at most $\Delta$. Almost surely, after preprocessing and after every update, the edge colouring written by the program is proper with colours in $\{1,\dots,\lfloor(1+\epsilon)\Delta\rfloor\}$. The expected number of steps of every single update is at most
--   $$C_2\,\Delta^{k_2},$$
--   where $C_2,k_2$ are absolute constants. Explicitly, $\Delta_\epsilon\le C_1\epsilon^{-2}(1+\ln(1/\epsilon))^{k_1}$.
--
--   This is contribution (II), the low-degree colouring ingredient: Lemma 9 applies it to subgraphs of degree $\Theta(\epsilon^{-5})$.
--
--   **Formalization Note.** The model and the readouts are those of the goal theorem (Theorem 1); see its Formalization Note.
--
--   Differences from the source:
--   - reading: a threshold Δ_ε = Õ(1/ε²) → a natural number Δ_ε with Δ_ε ≤ C₁(1/ε)²(1 + ln(1/ε))^{k₁}, C₁, k₁ absolute; the statement then holds for every Δ ≥ Δ_ε; reason: Õ hides factors polylogarithmic in 1/ε (PDF p. 3); Δ_ε has no closed form in the paper, so it is existential with this upper bound
--   - reading: expected update time poly(Δ) → E[steps of update t] ≤ C₂Δ^{k₂} for every update index t, C₂, k₂ absolute (independent of ε); reason: uniformity in ε is what Lemma 9 uses when it applies the theorem with D = Cε⁻⁵ (PDF p. 22)
--   - encoding: at most (1+ε)Δ colours → colours in {1, …, ⌊(1+ε)Δ⌋}; reason: the paper's colourings use a fixed palette; proper is implicit in edge colouring (PDF pp. 3, 17)
--   - reading: "the smallest maximum degree for which the static algorithm in [CHL+18] works" (PDF p. 19) → an existential Δ_ε with the Õ(1/ε²) upper bound; reason: the definition goes through [CHL+18], outside the paper; only the bound Δ_ε = Θ̃(ε⁻²) enters the statement
--   - reading: a randomized dynamic algorithm on a word RAM with O(log n)-bit words and unit-cost random words → one DynBrooks.Program on the published word RAM with word size a·⌈log₂(n+1)⌉ (a absolute), fixed before the vertex count and the degree bound; preprocessing receives the words n and min(Δ, n); reason: the paper names this model (PDF pp. 16, 37–38) and the program is chosen before n and Δ; min(Δ, n) loses nothing because degrees are at most n − 1
--   - reading: edge insertions and deletions in a simple graph of maximum degree at most Δ, against an oblivious adversary → every n ≥ 2 and every update list σ legal from the empty graph (DynColorWC.Main.IsLegalSeq Δ σ), quantified before the coin tape; reason: σ fixed before the coins is the oblivious adversary; an initial graph is built by insertions; for n ≤ 1 there are no edges
--   - reading: the algorithm maintains the colouring → almost surely, for every t ≤ |σ|, the completed state after t updates is reached and the colouring written by the machine (output triples u, v, q from the all-0 labelling) is proper for the current graph; reason: the LLL maintenance terminates only almost surely (PDF p. 13); the colouring must be the one the machine writes
--   - encoding: expected time of each update → for every update index t < |σ|, the step count updateTime of update t is measurable and its lower Lebesgue integral against the coin measure is bounded; reason: measurability makes the integral the expectation; a run that never completes has step count ⊤, so the bound also forces completion of every earlier update and of preprocessing almost surely
--   - reading: no statement about preprocessing time → preprocessing time is not bounded; reason: the theorem bounds only the update time; the paper computes its parameters in O(log Δ) time before the first update (PDF p. 37)
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Theorem 3, printed p. 18 (PDF p. 20); Δ_ε defined in §4, printed p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model
import Definitions.Def_DynEdgeColorLLL_Main_EdgeReadout
open MeasureTheory
open scoped ENNReal

namespace DynEdgeColorLLL.Main

/-- Theorem 3 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 18, PDF p. 20). For every
`0 < ε < 1` there are a threshold `Δ_ε = Õ(1/ε²)` and a randomized dynamic program maintaining a
proper edge colouring with colours in `{1, …, ⌊(1+ε)Δ⌋}` of a graph of maximum degree at most
`Δ ≥ Δ_ε`, with expected update time `poly(Δ)`: at most `C₂ Δ^{k₂}` with `C₂, k₂` absolute. -/
theorem theorem_3 :
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
              ENNReal.ofReal (C₂ * (Δ : ℝ) ^ k₂) := by sorry

end DynEdgeColorLLL.Main
