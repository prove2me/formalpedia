-- Prove2me | Theorems.Thm_AgnHalfMem_claim_B_5
-- name    : AgnHalfMem.claim_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:24.957015+00:00
-- url     : https://prove2.me/theorems/ce8512b0-49a7-48af-befe-989a63ba5516
-- title:
--   Claim B.5 — at a non-significant vertex, $\Pr[h\in\mathrm{Sig}(v)\mid E_v]\le 2^{-2r}$
-- statement:
--   In the setting of Appendix B (see Lemma B.4), let $v$ be a vertex of layer $i$ of $B$ that is not significant. Then
--   $$
--   \Pr\big[h\in\mathrm{Sig}(v)\,\big|\,E_v\big]=\sum_{h'\in\mathrm{Sig}(v)}P_{h|v}(h')\ \le\ 2^{-2r}.
--   $$
--   It bounds the probability that the truncated path stops for the second reason.
--
--   Differences from the source:
--   - encoding: standing assumptions of App. B stated once (p.29: 1/100 < c < 2/3, 3c/2 < γ² < 1, M a (k′,ℓ′)-extractor with error 2^{−r′} "for sufficiently large k′, ℓ′ and r′", B a branching program) → hypotheses AppBConstants c γ; ∃ K₀ (after c, γ) with K₀ ≤ k′, ℓ′, r′; M measurable in x with values in [−1,1] and IsL2Extractor μ M k′ ℓ′ r′; B a measurable deterministic BP on a finite state type S; reason: the section's standing assumptions are hypotheses of every claim; measurability is what makes the probabilities defined
--   - reading: γ with 3c/2 < γ² < 1; "k := γk" → 0 < γ; k = γk′ (appBk); reason: γ scales the exponents k, ℓ; the typo is corrected by p.37 "Recall that k = γk′"
--   - encoding: vertices of layers with at most 2^{ck′ℓ′} vertices, edges with labels A_e, P_{h|v} for Pr(v) > 0 → vertices (i, v) with v in one finite type S; edges (v, u) with A_e = {z | step i v z = u}; P_{h|v} := 0 when Pr(v) = 0; reason: Lean conventions for the layered graph; the zero posterior only arises on null vertices
--   - generalization: B of length m = 2^r and width at most 2^{ck′ℓ′} (p.30, “We assume B is a branching program with length m = 2^r and width at most 2^{ck′ℓ′}”) → any length T and any finite state type S, with no length or width bound; reason: the proof works at one vertex or edge and uses neither bound; programs of length 2^r and width at most 2^{ck′ℓ′} are instances
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.5, p.30 (proof p.31)

import Mathlib
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_AppBConstants
import Definitions.Def_AgnHalfMem_truncAlive

open MeasureTheory

universe u v w

namespace AgnHalfMem

/-- **Claim B.5.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.5, p.30: "If v is a non-significant vertex of B then
Pr[h ∈ Sig(v) | E_v] ≤ 2^{−2r}."

**Formalization Note.** The standing assumptions of App. B (p.29) are hypotheses: `c, γ` with
`AppBConstants c γ`; `M : X × H → [−1, 1]` measurable in `x`, a `(k′, ℓ′)`-L2-extractor with error
`2^{−r′}` for `k′, ℓ′, r′ ≥ K₀` ("sufficiently large", `K₀` chosen after `c, γ`); `ℓ = γℓ′/3`
(`appBl`), `r` as on p.29 (`appBr`), `k = γk′` (`appBk`); `B` a deterministic, measurable
program of length `T` on the states `S`. Vertices are pairs (layer `i`, state `v`); all
probabilities are under the joint law (`h` uniform, samples i.i.d. from `D_h`); `P_{h|v} = 0` when
`Pr(v) = 0`. `Pr[h ∈ Sig(v) | E_v]` is the `P_{h|v}`-mass of `Sig(v)`. -/
theorem claim_B_5 :
    ∀ c γ : ℝ, AppBConstants c γ →
    ∃ K₀ : ℝ,
    ∀ (H : Type u) [Fintype H] [Nonempty H] [MeasurableSpace H] [DiscreteMeasurableSpace H]
        (X : Type v) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (M : X → H → ℝ), (∀ h, Measurable fun x => M x h) →
        (∀ x h, M x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ k' l' r' : ℝ, IsL2Extractor μ M k' l' r' → K₀ ≤ k' → K₀ ≤ l' → K₀ ≤ r' →
      ∀ (S : Type w) [Fintype S] (T : ℕ) (B : BP S X T), B.IsMeasurableBP →
      ∀ (i : ℕ) (v : S), ¬ IsSignificant (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) (appBl γ l') →
        ∑ h, (Sig (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) (appBl γ l') (appBr γ k' l' r')).indicator
            (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) h ≤ (2 : ℝ) ^ (-(2 * appBr γ k' l' r')) := by sorry

end AgnHalfMem
