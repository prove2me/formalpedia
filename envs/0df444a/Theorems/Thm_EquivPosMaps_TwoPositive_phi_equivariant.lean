-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_phi_equivariant
-- name    : EquivPosMaps.TwoPositive.phi_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:43.537613+00:00
-- url     : https://prove2.me/theorems/be7ada2e-e1ec-4ac4-893a-993077d572ef
-- title:
--   Proof of Proposition 3.1: equivariance of the family
-- statement:
--   Let $n\geq3$, let $\alpha,\beta\in\mathbb R$, and let $U\in M_n(\mathbb C)$ be unitary. Set $V=\overline U\otimes U$. For every $X\in M_n(\mathbb C)$,
--
--   $$
--   \Phi_{\alpha,\beta,n}(UXU^*)=V\Phi_{\alpha,\beta,n}(X)V^*.
--   $$
--
--   This is the displayed equivariance computation in the proof of Proposition 3.1. It supplies the structural condition used in the positivity and 2-positivity criteria. The conjugation on the first tensor factor is essential.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, pp. 6–7, proof of Proposition 3.1, “Choose V = Ū ⊗ U …”

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- The equivariance display in the proof of Proposition 3.1, pp. 6–7. -/
theorem phi_equivariant (n : ℕ) (hn : 3 ≤ n) (α β : ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    phi n α β ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) =
      (((U : Matrix (Fin n) (Fin n) ℂ).map star) ⊗ₖ
        (U : Matrix (Fin n) (Fin n) ℂ)) * phi n α β X *
          ((((U : Matrix (Fin n) (Fin n) ℂ).map star) ⊗ₖ
            (U : Matrix (Fin n) (Fin n) ℂ))ᴴ) := by sorry

end EquivPosMaps.TwoPositive
