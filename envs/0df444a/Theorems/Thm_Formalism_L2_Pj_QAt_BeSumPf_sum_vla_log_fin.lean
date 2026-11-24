-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_BeSumPf_sum_vla_log_fin
-- name    : Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:14.34388+00:00
-- url     : https://prove2.me/theorems/b9b4b10d-6d34-4665-90b4-bf7e909e9988
-- title:
--   Be Sum Pf: sum vla log fin
-- statement:
--   The Be Sum Pf construction uses the sum vla log fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L21-L42

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

theorem Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin (I : Ideal (𝓞 K)) (hI : I ≠ 0) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ v, vla v I ≠ 0 → v ∈ s) :
    ∑ v ∈ s, (vla v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) = Real.log (Ideal.absNorm I : ℝ) := by sorry
