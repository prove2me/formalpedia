-- Prove2me | solution 1 for natDegree_crouzeixProductRemainderPolynomial_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:48.010801+00:00
-- url     : https://prove2.me/submissions/cdfae115-685e-4e94-b338-651cb0eee405

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    (crouzeixProductRemainderPolynomial Omega p).natDegree < p.natDegree := by
  unfold crouzeixProductRemainderPolynomial
  have hle :
      (∑ i ∈ Finset.range p.natDegree,
        Polynomial.monomial i
          ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            contourIntegral
              (fun z => star (Polynomial.eval z p) *
                (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
              Omega.boundaryParam)).natDegree ≤ p.natDegree - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.le_pred_of_lt (Finset.mem_range.mp hi))
  exact hle.trans_lt (Nat.sub_lt hp (by norm_num))
