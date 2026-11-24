-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_map_pow_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.map_pow_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:29.450869+00:00
-- url     : https://prove2.me/theorems/a8d47fff-7ab1-4ac1-ad64-576571cd66ec
-- title:
--   Exp Uniq Jet: map pow mem
-- statement:
--   The Exp Uniq Jet construction uses the map pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L86-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L86-L96

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.map_pow_mem {κ κ' : Type} {m m' : ℕ} (f : Jet R κ m →ₐ[R] Jet R κ' m')
    (hf : ∀ j, f (zz m j) ∈ Ij R κ' m') (k : ℕ) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    f p ∈ Ij R κ' m' ^ k := by sorry
