-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_8
-- name    : DynEdgeColorLLL.Main.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:02.576411+00:00
-- url     : https://prove2.me/theorems/5ec8a7f7-d2fa-43c0-916c-ee158a682ce9
-- title:
--   Lemma 8 — dynamic random $F$-way splitting in $O(1)$ expected time, recourse $1+e^{-\Omega(\delta^2\Delta/F)}$
-- statement:
--   Let $\Delta$ bound the maximum degree of a dynamic graph, and let $F\in\{1,\dots,\lfloor\Delta\rfloor\}$ and $0<\delta\le1$ satisfy $\delta^2\Delta/F\ge C_0\log\Delta$, with $C_0$ an absolute constant (the reading of $\delta^2\Delta/F=\omega(\log\Delta)$). Then there is a randomized dynamic program with the following guarantee, for every $n\ge2$ and every sequence of insertions and deletions fixed in advance that keeps the graph simple with maximum degree at most $\Delta$:
--   1. almost surely, after preprocessing and after every update, the written labelling partitions the current graph into $F$ subgraphs, each of maximum degree at most $(1+\delta)\Delta/F$;
--   2. the expected number of steps of every update is at most $C$;
--   3. the expected recourse of every update, the edge membership changes summed over the $F$ subgraphs, is at most
--   $$1+e^{-c\,\delta^2\Delta/F}.$$
--   Here $C_0,C,c>0$ are absolute constants.
--
--   Iterated, the lemma reduces the degree; Lemma 9 uses it once with $\delta=\epsilon$ and $F=\lfloor\Delta/D\rfloor$.
--
--   **Formalization Note.** The partition is the program's output, read as triples $u,v,j$ ("edge $\{u,v\}$ is in part $j$"). The program may depend on $\Delta,F,\delta$, which the lemma fixes first. Updates must be legal for the integer bound $\lfloor\Delta\rfloor$.
--
--   Differences from the source:
--   - reading: δ²Δ/F = ω(log Δ) → δ²Δ/F ≥ C₀ log Δ for an absolute C₀; reason: covers every family the ω-hypothesis covers once Δ is large; it is what the proof uses (q·poly(Δ) = O(1))
--   - reading: expected update time O(1) and expected recourse 1 + exp(−Ω(δ²Δ/F)) → E[steps] ≤ C and E[recourse] ≤ 1 + exp(−c·δ²Δ/F) for every update, C and c > 0 absolute; reason: the asymptotic notation with explicit absolute constants
--   - reading: there is a dynamic algorithm (Δ, F, δ given) → a program chosen after Δ, F, δ and before n and the update sequence; reason: the lemma fixes Δ, F and δ before asserting the algorithm
--   - encoding: a dynamic graph of maximum degree at most Δ (Δ real, F ≤ ⌊Δ⌋) → update lists legal for the integer degree bound ⌊Δ⌋; reason: degrees are integers, so degree ≤ Δ iff degree ≤ ⌊Δ⌋
--   - reading: partitions G into F subgraphs → almost surely, at every completed state, every current edge carries a written part label in {1, …, F} and every part has maximum degree at most (1+δ)Δ/F; reason: the partition is maintained after every update; the LLL maintenance succeeds almost surely
--   - encoding: expected update time and expected recourse → measurable step count and recourse, bounded lower Lebesgue integrals; reason: measurability makes the integrals expectations
--   - encoding: graphs of any size → n ≥ 2 vertices, word size a·⌈log₂(n+1)⌉ with a absolute; reason: n ≤ 1 has no edges
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 8, printed p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model
import Definitions.Def_DynEdgeColorLLL_Main_EdgeReadout
open MeasureTheory
open scoped ENNReal

namespace DynEdgeColorLLL.Main

/-- Lemma 8 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 20, PDF p. 22). Let `Δ` bound
the maximum degree of a dynamic graph and let `F ∈ {1, …, ⌊Δ⌋}`, `0 < δ ≤ 1` with
`δ²Δ/F = ω(log Δ)` (read: `δ²Δ/F ≥ C₀ log Δ` for an absolute `C₀`). There is a dynamic program
writing a partition of the current graph into `F` subgraphs of maximum degree at most
`(1+δ)Δ/F` after every update, almost surely, with `O(1)` expected update time and expected
recourse (edge membership changes summed over the subgraphs) at most `1 + exp(−c δ²Δ/F)`. -/
theorem lemma_8 :
    ∃ (a : ℕ) (C₀ C c : ℝ), 0 < c ∧
      ∀ (Δ : ℝ) (F : ℕ) (δ : ℝ), 1 ≤ F → F ≤ ⌊Δ⌋₊ → 0 < δ → δ ≤ 1 →
        C₀ * Real.log Δ ≤ δ ^ 2 * Δ / F →
        ∃ P : DynBrooks.Program,
          ∀ (n : ℕ), 2 ≤ n → ∀ σ : List (DynBrooks.Update n),
            DynColorWC.Main.IsLegalSeq ⌊Δ⌋₊ σ →
            (∀ᵐ ω ∂(DynBrooks.coinMeasure (DynColorWC.Main.wordSize a n)),
              ∀ t ≤ σ.length,
                (DynColorWC.Main.stateAt P ω [n, min ⌊Δ⌋₊ n] σ t).isSome ∧
                IsDegreeBoundedPartition F ((1 + δ) * Δ / F) (DynColorWC.Main.graphAt σ t)
                  (edgeColorAt P ω [n, min ⌊Δ⌋₊ n] σ t)) ∧
            ∀ t < σ.length,
              Measurable (fun ω : ℕ → BitVec (DynColorWC.Main.wordSize a n) =>
                ((DynColorWC.Main.updateTime P ω [n, min ⌊Δ⌋₊ n] σ t : ℕ∞) : ℝ≥0∞)) ∧
              ∫⁻ ω, ((DynColorWC.Main.updateTime P ω [n, min ⌊Δ⌋₊ n] σ t : ℕ∞) : ℝ≥0∞)
                  ∂(DynBrooks.coinMeasure (DynColorWC.Main.wordSize a n)) ≤ ENNReal.ofReal C ∧
              Measurable (fun ω : ℕ → BitVec (DynColorWC.Main.wordSize a n) =>
                ((partRecourse P ω [n, min ⌊Δ⌋₊ n] F σ t : ℕ) : ℝ≥0∞)) ∧
              ∫⁻ ω, ((partRecourse P ω [n, min ⌊Δ⌋₊ n] F σ t : ℕ) : ℝ≥0∞)
                  ∂(DynBrooks.coinMeasure (DynColorWC.Main.wordSize a n)) ≤
                ENNReal.ofReal (1 + Real.exp (-(c * (δ ^ 2 * Δ / F)))) := by sorry

end DynEdgeColorLLL.Main
