-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_BeSumPf_vla_ne_zero_iff
-- name    : Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:02.737532+00:00
-- url     : https://prove2.me/theorems/213709e4-b787-419e-b8a3-d5ec5d86beff
-- title:
--   Be Sum Pf: vla ne zero iff
-- statement:
--   The Be Sum Pf construction uses the vla ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L13-L16

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField IsDedekindDomain
open Formalism.L2.Pj.QAt.BeSumPf
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff (la : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    vla la I ≠ 0 ↔ la.asIdeal ∣ I := by sorry
