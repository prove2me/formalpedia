-- Prove2me | Theorems.Thm_CondGeoVerif_eq_B_5
-- name    : CondGeoVerif.eq_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:39:52.965945+00:00
-- url     : https://prove2.me/theorems/4be081a7-5338-4f90-9114-01d0a5649250
-- title:
--   (B.5) — $\mathrm{TV}(P^n,Q^{\otimes n})\le\frac12\sqrt{\chi^2}<1/6$
-- statement:
--   Let $1\le k\le D$, $0<\eta<1/2$, $f$ Borel, $j\in\{0,1\}$, and let $e$ be a jointly measurable allocation with $e(u,\cdot)\in\mathcal E_j$ for every $u$. Let $Q$ be the random-noise anchor, $P_V$ the hidden-frame alternatives, $V$ uniform on the Stiefel manifold, and $P^n=\mathbb E_VP_V^{\otimes n}$ with the same random frame for all $n$ observations. Then
--   $$1+\chi^2(P^n\|Q^{\otimes n})=\mathbb E_{V,W}K(V,W)^n ,$$
--   and if $n\le\sqrt D/(100k)$ when $j=0$, or $n\le D/(100k^2)$ when $j=1$,
--   $$\mathrm{TV}(P^n,Q^{\otimes n})\le\tfrac12\sqrt{\chi^2(P^n\|Q^{\otimes n})}<1/6.\qquad(B.5)$$
--   No test with fewer observations distinguishes the null from the mixture.
--
--   Differences from the source:
--   - generalization: e from Lemma B.2 → any jointly measurable allocation with sections in E_j; reason: the paper's allocation is one such
--   - encoding: P_V defined by its regression for each frame; V uniform → a family V ↦ P_V with IsLabelLaw for every orthonormal V; a rotation-invariant law on the Stiefel set; TV the published sup_A |μ(A) − ν(A)|; reason: the values off the Stiefel set are irrelevant since the frame law is carried by it; same quantities
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §B.4, p.27 (PDF p.30), eq. (B.5)

import Mathlib
import Definitions.Def_CondGeoVerif_hiddenErr
import Definitions.Def_CondGeoVerif_IsRotInvStiefelLaw
import Definitions.Def_CondGeoVerif_risk
import Definitions.Def_TotalVariationDist

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

namespace CondGeoVerif

/-- **Indistinguishability (B.5)** (Chen, *The Conditional Geometry of Statistical Verification*,
manuscript, October 2026, sha256 07a66d18…, §B.4, p.27 = PDF p.30). Let `e` be a jointly measurable
allocation with `e(u, ·) ∈ E_j` for every `u`, `Q` the random-noise anchor, `P_V` the hidden-frame
alternatives, `V` uniform on the Stiefel manifold, and `Pⁿ = E_V P_V^{⊗n}` with the same random
frame shared across all `n` observations. Then `1 + χ²(Pⁿ‖Q^{⊗n}) = E_{V,W}K(V, W)ⁿ`, and if
`n ≤ √D/(100k)` (for `j = 0`) or `n ≤ D/(100k²)` (for `j = 1`),
`TV(Pⁿ, Q^{⊗n}) ≤ (1/2)√(χ²(Pⁿ‖Q^{⊗n})) < 1/6`.

**Formalization Note** The family `V ↦ P_V` is required to be the alternative for every
orthonormal `V` (its values elsewhere are irrelevant, since the frame law is carried by the
Stiefel set). TV is the published `MarkovChainCLT.tvDist`, `sup_A |μ(A) − ν(A)|`. -/
theorem eq_B_5 {k D : ℕ} (hk : 1 ≤ k) (hkD : k ≤ D) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (f : Vec k → Bool) (hf : Measurable f) (j : Fin 2) (e : Vec k → Vec k → ℝ)
    (he : Measurable (fun p : Vec k × Vec k => e p.1 p.2)) (heE : ∀ u, e u ∈ errorAllocs j η k)
    (Q : ProbabilityMeasure (Vec (k + D) × Bool))
    (hQ : IsLabelLaw (Q : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) (fun _ => η))
    (PV : Matrix (Fin D) (Fin k) ℝ → ProbabilityMeasure (Vec (k + D) × Bool))
    (hPV : ∀ V ∈ stiefel D k,
      IsLabelLaw (PV V : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) (hiddenErr e V))
    (ν : ProbabilityMeasure (Matrix (Fin D) (Fin k) ℝ))
    (hν : IsRotInvStiefelLaw (ν : Measure (Matrix (Fin D) (Fin k) ℝ))) (n : ℕ)
    (hn0 : j = 0 → (n : ℝ) ≤ Real.sqrt D / (100 * k))
    (hn1 : j = 1 → (n : ℝ) ≤ D / (100 * k ^ 2)) :
    let Pn := frameMixture (ν : Measure (Matrix (Fin D) (Fin k) ℝ))
      (fun V => (PV V : Measure (Vec (k + D) × Bool))) n
    let Qn := Measure.pi (fun _ : Fin n => (Q : Measure (Vec (k + D) × Bool)))
    1 + chiSq Pn Qn = ∫ p, likKernel (Q : Measure (Vec (k + D) × Bool))
        (PV p.1 : Measure (Vec (k + D) × Bool)) (PV p.2 : Measure (Vec (k + D) × Bool)) ^ n
        ∂((ν : Measure (Matrix (Fin D) (Fin k) ℝ)).prod (ν : Measure (Matrix (Fin D) (Fin k) ℝ))) ∧
    MarkovChainCLT.tvDist Pn Qn ≤ (1 / 2) * Real.sqrt (chiSq Pn Qn) ∧
    (1 / 2) * Real.sqrt (chiSq Pn Qn) < 1 / 6 := by sorry

end CondGeoVerif
