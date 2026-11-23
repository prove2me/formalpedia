-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jetMap_alt_alt
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.jetMap_alt_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:57.173868+00:00
-- url     : https://prove2.me/theorems/3bd4c2ae-81d5-4a7c-be5f-2573da8e46cb
-- title:
--   Exp Uniq Jet: jet Map alt alt
-- statement:
--   The Exp Uniq Jet construction uses the jet Map alt alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L35-L39

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.jetMap_alt_alt {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R) (hφ : ∀ i, φ i ∈ orig R κ') (j : κ) :
    jetMap (m := m) φ hφ (zz m j) = Ideal.Quotient.mk _ (φ j) := by sorry
