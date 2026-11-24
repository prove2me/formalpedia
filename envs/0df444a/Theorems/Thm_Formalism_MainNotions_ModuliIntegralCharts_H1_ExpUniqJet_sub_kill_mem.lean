-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_sub_kill_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.sub_kill_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:00:33.421882+00:00
-- url     : https://prove2.me/theorems/4a5c6bff-5af5-4419-b5ed-b9e1b24443d9
-- title:
--   Exp Uniq Jet: sub kill mem
-- statement:
--   The Exp Uniq Jet construction uses the sub kill mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L229-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L229-L238

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
variable {n : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.sub_kill_mem (m : ℕ) (i : Fin 2) (e : Jet R (Fin 2 × Fin n) m) : e - kill m i e ∈ Kp m i := by sorry
