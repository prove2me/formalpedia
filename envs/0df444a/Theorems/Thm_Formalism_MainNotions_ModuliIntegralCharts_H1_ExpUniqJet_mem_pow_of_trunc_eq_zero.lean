-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_mem_pow_of_trunc_eq_zero
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.mem_pow_of_trunc_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:12.55743+00:00
-- url     : https://prove2.me/theorems/a75b528a-25ca-491a-bfd7-9a82d4152034
-- title:
--   Exp Uniq Jet: mem pow of trunc eq zero
-- statement:
--   The Exp Uniq Jet construction uses the mem pow of trunc eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L41-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L41-L53

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.mem_pow_of_trunc_eq_zero {κ : Type} {m : ℕ} (p : Jet R κ (m + 1))
    (h : (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) p = 0) : p ∈ Ij R κ (m + 1) ^ (m + 1) := by sorry
