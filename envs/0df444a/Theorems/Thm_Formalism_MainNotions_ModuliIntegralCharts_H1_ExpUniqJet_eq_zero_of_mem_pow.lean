-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_eq_zero_of_mem_pow
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.eq_zero_of_mem_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:00:53.039583+00:00
-- url     : https://prove2.me/theorems/42084a5f-0d6e-417c-9c69-d3951a71da3f
-- title:
--   Exp Uniq Jet: eq zero of mem pow
-- statement:
--   The Exp Uniq Jet construction uses the eq zero of mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L29-L33

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.eq_zero_of_mem_pow {κ : Type} {m k : ℕ} (hk : m + 1 ≤ k) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    p = 0 := by sorry
