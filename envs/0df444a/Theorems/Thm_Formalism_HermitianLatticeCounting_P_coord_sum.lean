-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_coord_sum
-- name    : Formalism.HermitianLatticeCounting.P.coord_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:40:19.803806+00:00
-- url     : https://prove2.me/theorems/e809bf4a-1591-5097-a759-be0e5eed9861
-- title:
--   P: coord sum
-- statement:
--   The P construction uses the coord sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LanglandsParameterEquivariant.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LanglandsParameterEquivariant.lean#L16-L22

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

theorem Formalism.HermitianLatticeCounting.P.coord_sum {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ξ : Fin n → V) (a : Fin n) :
    LLmap LinearMap.id a (∑ c, ξ c ⊗ₜ[ℂ] (Pi.single c (1 : ℂ) : Fin n → ℂ)) = ξ a := by sorry
