-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_det_sesquilinear_le_gramSchmidt
-- name    : Formalism.HermitianLatticeCounting.P.norm_det_sesquilinear_le_gramSchmidt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:38.327447+00:00
-- url     : https://prove2.me/theorems/ab31b478-e503-4d00-92ac-b471215c0f43
-- title:
--   P: norm det sesquilinear le gram Schmidt
-- statement:
--   The P construction uses the norm det sesquilinear le gram Schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L348-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L348-L409

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace

theorem Formalism.HermitianLatticeCounting.P.norm_det_sesquilinear_le_gramSchmidt {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖) {j : ℕ} (y : Fin j → V₁) (y' : Fin j → V₂) :
    ‖(Matrix.of fun a b => B (y a) (y' b)).det‖ ≤
      c ^ j * (∏ i, ‖gramSchmidt ℂ y i‖) * ∏ k, ‖gramSchmidt ℂ y' k‖ := by sorry
