-- Prove2me | Theorems.Thm_AgnHalfMem_claim_B_7
-- name    : AgnHalfMem.claim_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:44.938137+00:00
-- url     : https://prove2.me/theorems/1ce56246-5b74-47e4-b77a-c0b97967acd5
-- title:
--   Claim B.7 — a non-significant leaf has correlation $O(2^{-r/2})$ with the hidden column
-- statement:
--   In the setting of Appendix B (see Lemma B.4), let $v$ be a non-significant leaf of $B$ with label $\tilde h_v$. Then
--   $$
--   \mathbb E_h\Big[\,\big|\mathbb E_{x\sim\mu}[\tilde h_v(x)\,M(x,h)]\big|\ \Big|\ E_v\Big]\ \le\ A\cdot 2^{-r/2},
--   $$
--   with $A$ depending only on $c,\gamma$. Since $\mathrm{err}_h(\tilde h_v)=\tfrac12(1-\mathbb E_x[\tilde h_v(x)M(x,h)])$, the output at such a leaf is a weak learner only with small probability.
--
--   Differences from the source:
--   - encoding: standing assumptions of App. B stated once (p.29: 1/100 < c < 2/3, 3c/2 < γ² < 1, M a (k′,ℓ′)-extractor with error 2^{−r′} "for sufficiently large k′, ℓ′ and r′", B a branching program) → hypotheses AppBConstants c γ; ∃ K₀ (after c, γ) with K₀ ≤ k′, ℓ′, r′; M measurable in x with values in [−1,1] and IsL2Extractor μ M k′ ℓ′ r′; B a measurable deterministic BP on a finite state type S; reason: the section's standing assumptions are hypotheses of every claim; measurability is what makes the probabilities defined
--   - reading: γ with 3c/2 < γ² < 1; "k := γk" → 0 < γ; k = γk′ (appBk); reason: γ scales the exponents k, ℓ; the typo is corrected by p.37 "Recall that k = γk′"
--   - encoding: vertices of layers with at most 2^{ck′ℓ′} vertices, edges with labels A_e, P_{h|v} for Pr(v) > 0 → vertices (i, v) with v in one finite type S; edges (v, u) with A_e = {z | step i v z = u}; P_{h|v} := 0 when Pr(v) = 0; reason: Lean conventions for the layered graph; the zero posterior only arises on null vertices
--   - reading: O(2^{−r/2}) → A·2^{−r/2} with A chosen after c, γ; reason: standard meaning of O
--   - generalization: B of length m = 2^r and width at most 2^{ck′ℓ′} (p.30, “We assume B is a branching program with length m = 2^r and width at most 2^{ck′ℓ′}”) → any length T and any finite state type S, with no length or width bound; reason: the proof works at one vertex or edge and uses neither bound; programs of length 2^r and width at most 2^{ck′ℓ′} are instances
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.7, p.32 (proof pp.32–33)

import Mathlib
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_AppBConstants
import Definitions.Def_AgnHalfMem_truncAlive

open MeasureTheory

universe u v w

namespace AgnHalfMem

/-- **Claim B.7.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.7, p.32: "If v is a non-significant leaf, then
E_h[ |E_{x∼µ}[h̃_v(x) · M(x, h)]| | E_v ] ≤ O(2^{−r/2})."

**Formalization Note.** The standing assumptions of App. B (p.29) are hypotheses: `c, γ` with
`AppBConstants c γ`; `M : X × H → [−1, 1]` measurable in `x`, a `(k′, ℓ′)`-L2-extractor with error
`2^{−r′}` for `k′, ℓ′, r′ ≥ K₀` ("sufficiently large", `K₀` chosen after `c, γ`); `ℓ = γℓ′/3`
(`appBl`), `r` as on p.29 (`appBr`), `k = γk′` (`appBk`); `B` a deterministic, measurable
program of length `T` on the states `S`. Vertices are pairs (layer `i`, state `v`); all
probabilities are under the joint law (`h` uniform, samples i.i.d. from `D_h`); `P_{h|v} = 0` when
`Pr(v) = 0`. The conditional expectation over `h` given `E_v` is the `P_{h|v}`-average; `O(·)` is a
constant `A`; the leaf label `h̃_v` is `sgn ∘ B.out i v`. -/
theorem claim_B_7 :
    ∀ c γ : ℝ, AppBConstants c γ →
    ∃ K₀ A : ℝ, 0 < A ∧
    ∀ (H : Type u) [Fintype H] [Nonempty H] [MeasurableSpace H] [DiscreteMeasurableSpace H]
        (X : Type v) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (M : X → H → ℝ), (∀ h, Measurable fun x => M x h) →
        (∀ x h, M x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ k' l' r' : ℝ, IsL2Extractor μ M k' l' r' → K₀ ≤ k' → K₀ ≤ l' → K₀ ≤ r' →
      ∀ (S : Type w) [Fintype S] (T : ℕ) (B : BP S X T), B.IsMeasurableBP →
      ∀ (i : ℕ) (v : S), B.IsLeafAt i v → ¬ IsSignificant (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) (appBl γ l') →
        ∑ h, vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v h * |∫ x, sgn (B.out i v x) * M x h ∂μ| ≤
          A * (2 : ℝ) ^ (-(appBr γ k' l' r' / 2)) := by sorry

end AgnHalfMem
