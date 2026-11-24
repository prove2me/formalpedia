-- Prove2me | Theorems.Thm_Formalism_UG_P_easyc_inclE_mem
-- name    : Formalism.UG.P.easyc_inclE_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:38.995814+00:00
-- url     : https://prove2.me/theorems/c226a5ab-aab4-4705-87e9-5882bf95b2b3
-- title:
--   P: easyc incl E mem
-- statement:
--   The P construction uses the easyc incl E mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L36-L40

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem Formalism.UG.P.easyc_inclE_mem (e : E) (he : e ∈ intOE E) :
    inclE (F := F) R e ∈ tensInt (F := F) R (intOE E) S₂ := by sorry
