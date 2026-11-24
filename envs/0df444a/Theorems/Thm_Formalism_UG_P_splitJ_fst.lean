-- Prove2me | Theorems.Thm_Formalism_UG_P_splitJ_fst
-- name    : Formalism.UG.P.splitJ_fst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:59.663225+00:00
-- url     : https://prove2.me/theorems/3a1c0e42-0ec0-4fd0-88a5-1f79bf47b6f6
-- title:
--   P: split J fst
-- statement:
--   The P construction uses the split J fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L37-L39

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

theorem Formalism.UG.P.splitJ_fst (J₁ : Matrix n n R) : (splitJ J₁).map Prod.fst = J₁ := by sorry
