-- Prove2me | Theorems.Thm_Formalism_UG_P_split_map_snd_mul
-- name    : Formalism.UG.P.split_map_snd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:15.109401+00:00
-- url     : https://prove2.me/theorems/987e56a6-2da8-4bc7-9af1-6debd1e5748e
-- title:
--   P: split map snd mul
-- statement:
--   The P construction uses the split map snd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L22-L25

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

theorem Formalism.UG.P.split_map_snd_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.snd = M.map Prod.snd * N.map Prod.snd := by sorry
