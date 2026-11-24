-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_LL_tmul
-- name    : Formalism.HermitianLatticeCounting.P.LL_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:51.625087+00:00
-- url     : https://prove2.me/theorems/0e20646d-38e5-43a5-98c4-70b758ebae67
-- title:
--   P: LL tmul
-- statement:
--   The P construction uses the LL tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LanglandsParameterEquivariant.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LanglandsParameterEquivariant.lean#L12-L14

import Definitions.Def_Formalism_FlagUnipotentLattices_InterlaceBlocksW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.LL_tmul {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] {n : ℕ}
    (ℓ : V →ₗ[ℂ] U) (a : Fin n) (v : V) (y : Fin n → ℂ) : LLmap ℓ a (v ⊗ₜ[ℂ] y) = y a • ℓ v := by sorry
