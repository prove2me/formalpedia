-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_mulVec_mul
-- name    : Formalism.UG.P.levelv_mulVec_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:35.058416+00:00
-- url     : https://prove2.me/theorems/e0ae1a23-30da-4900-818e-08b105a1db3e
-- title:
--   P: levelv mul Vec mul
-- statement:
--   The P construction uses the levelv mul Vec mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L270-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L270-L272

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

theorem Formalism.UG.P.levelv_mulVec_mul (k l : GL n R) (x : n → R) :
    ((k * l : GL n R) : Matrix n n R) *ᵥ x = (k : Matrix n n R) *ᵥ ((l : Matrix n n R) *ᵥ x) := by sorry
