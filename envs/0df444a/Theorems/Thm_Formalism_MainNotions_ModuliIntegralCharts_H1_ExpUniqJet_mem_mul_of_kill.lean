-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_mem_mul_of_kill
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.mem_mul_of_kill
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:31.655625+00:00
-- url     : https://prove2.me/theorems/62a15922-a032-4896-aaec-97815243407c
-- title:
--   Exp Uniq Jet: mem mul of kill
-- statement:
--   The Exp Uniq Jet construction uses the mem mul of kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L240-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L240-L265

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.mem_mul_of_kill (m : ℕ) (e : Jet R (Fin 2 × Fin n) m) (h0 : kill m 0 e = 0) (h1 : kill m 1 e = 0) :
    e ∈ Kp m 0 * Kp m 1 := by sorry
