-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nrmOf_le_one_iff
-- name    : Formalism.L2.Pj.nrmOf_le_one_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:02.06962+00:00
-- url     : https://prove2.me/theorems/4ce6229a-7a31-5b1c-a878-408c686e2aac
-- title:
--   Pj: nrm Of le one iff
-- statement:
--   The Pj construction uses the nrm Of le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L174-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L174-L181

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem Formalism.L2.Pj.nrmOf_le_one_iff {v : EReal} (hv : v ≠ ⊥) : nrmOf la v ≤ 1 ↔ 0 ≤ v := by sorry
