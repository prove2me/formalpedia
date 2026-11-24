-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_inv_mulVec
-- name    : Formalism.UG.P.levelv_inv_mulVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:37.677034+00:00
-- url     : https://prove2.me/theorems/e50ee6b4-dd29-4516-8324-d90bd4c5e53e
-- title:
--   P: levelv inv mul Vec
-- statement:
--   The P construction uses the levelv inv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L274-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L274-L276

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelv_inv_mulVec (k : GL n R) (x : n → R) :
    ((k⁻¹ : GL n R) : Matrix n n R) *ᵥ ((k : Matrix n n R) *ᵥ x) = x := by sorry
