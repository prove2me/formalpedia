-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_mulVec_inv
-- name    : Formalism.UG.P.levelv_mulVec_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:59.893677+00:00
-- url     : https://prove2.me/theorems/479da21a-1f66-4707-82aa-2b931e427c03
-- title:
--   P: levelv mul Vec inv
-- statement:
--   The P construction uses the levelv mul Vec inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L278-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L278-L280

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

theorem Formalism.UG.P.levelv_mulVec_inv (k : GL n R) (x : n → R) :
    (k : Matrix n n R) *ᵥ (((k⁻¹ : GL n R) : Matrix n n R) *ᵥ x) = x := by sorry
