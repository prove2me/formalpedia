-- Prove2me | solution 1 for spectrum_aeval_subset_closedBall_eval_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:32:03.666259+00:00
-- url     : https://prove2.me/submissions/547b8775-dd9a-4520-ba0e-b2c148fe00cb

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall (Polynomial.eval c p)
        (polynomialSupNorm (p - Polynomial.C (Polynomial.eval c p)) K) := by
  have hcentered :=
    spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound
      A c hA hK hsymm p
  have hshift : spectrum ℂ (Polynomial.aeval A p -
      Polynomial.eval c p • (1 : E →L[ℂ] E)) =
      spectrum ℂ (Polynomial.aeval A p) -
        ({Polynomial.eval c p} : Set ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq]
  intro z hz
  have hzcentered : z - Polynomial.eval c p ∈
      spectrum ℂ (Polynomial.aeval A p -
        Polynomial.eval c p • (1 : E →L[ℂ] E)) := by
    rw [hshift]
    exact ⟨z, hz, Polynomial.eval c p, Set.mem_singleton _, rfl⟩
  have hzball := hcentered hzcentered
  rw [Metric.mem_closedBall, dist_zero_right] at hzball
  rwa [Metric.mem_closedBall, dist_eq_norm]
