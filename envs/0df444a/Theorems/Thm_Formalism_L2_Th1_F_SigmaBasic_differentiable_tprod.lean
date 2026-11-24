-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaBasic_differentiable_tprod
-- name    : Formalism.L2.Th1.F.SigmaBasic.differentiable_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:50.763771+00:00
-- url     : https://prove2.me/theorems/5a87ead0-1042-4a52-bfb4-caa979bfdd45
-- title:
--   Sigma Basic: differentiable tprod
-- statement:
--   The Sigma Basic construction uses the differentiable tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaBasic.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaBasic.lean#L28-L35

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaBasic

theorem Formalism.L2.Th1.F.SigmaBasic.differentiable_tprod (h : SigmaProdLU) (L : PeriodPair) :
    Differentiable ℂ (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) := by sorry
