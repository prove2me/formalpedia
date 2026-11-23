-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_sesquilinear_change_basis
-- name    : Formalism.HermitianLatticeCounting.P.det_sesquilinear_change_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:51.875257+00:00
-- url     : https://prove2.me/theorems/fe1125a7-cc28-47d7-ab8f-e0a1fd371ecb
-- title:
--   P: det sesquilinear change basis
-- statement:
--   The P construction uses the det sesquilinear change basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L265-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L265-L277

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
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem Formalism.HermitianLatticeCounting.P.det_sesquilinear_change_basis {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {j : ℕ} (L L' : Matrix (Fin j) (Fin j) ℂ) (g : Fin j → V₁)
    (g' : Fin j → V₂) :
    (Matrix.of fun a b => B (∑ i, L a i • g i) (∑ k, L' b k • g' k)).det =
      L.det * (Matrix.of fun i k => B (g i) (g' k)).det * star L'.det := by sorry
