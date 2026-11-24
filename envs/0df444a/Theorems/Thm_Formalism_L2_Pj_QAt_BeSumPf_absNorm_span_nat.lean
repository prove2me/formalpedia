-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_BeSumPf_absNorm_span_nat
-- name    : Formalism.L2.Pj.QAt.BeSumPf.absNorm_span_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:27.021011+00:00
-- url     : https://prove2.me/theorems/dc826cd6-405d-4a9b-a700-53043b5086dd
-- title:
--   Be Sum Pf: abs Norm span nat
-- statement:
--   The Be Sum Pf construction uses the abs Norm span nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L44-L49

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

theorem Formalism.L2.Pj.QAt.BeSumPf.absNorm_span_nat (n' : ℕ) :
    Ideal.absNorm (Ideal.span {(n' : 𝓞 K)}) = n' ^ Module.finrank ℚ K := by sorry
