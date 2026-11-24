-- Prove2me | Theorems.Thm_Formalism_UG_P_split_cT_snd
-- name    : Formalism.UG.P.split_cT_snd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:14.655061+00:00
-- url     : https://prove2.me/theorems/05537d15-13e4-4105-9c0d-7fb1b1a1e0e2
-- title:
--   P: split c T snd
-- statement:
--   The P construction uses the split c T snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L32-L35

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.split_cT_snd (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.snd = (g.map Prod.fst)ᵀ := by sorry
