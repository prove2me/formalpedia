-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_aug_sc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.aug_sc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:00:52.240792+00:00
-- url     : https://prove2.me/theorems/55eb42ed-7452-49bd-bbc8-393c78ee4ab3
-- title:
--   Exp Uniq Jet: aug sc
-- statement:
--   The Exp Uniq Jet construction uses the aug sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L107-L113

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.aug_sc {κ : Type} (m : ℕ) (c : R) (p : Jet R κ m) :
    (jetAug : Jet R κ m →ₐ[R] R) (sc m c p) = (jetAug : Jet R κ m →ₐ[R] R) p := by sorry
