-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_law
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.law
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:34.066307+00:00
-- url     : https://prove2.me/theorems/2e62ae22-cde0-47cf-81fc-6820e4a7eadc
-- title:
--   Exp Uniq Loc: law
-- statement:
--   The Exp Uniq Loc construction uses the law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqLoc.lean#L127-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqLoc.lean#L127-L164

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {n : ℕ}
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.law (M : ℕ) : ∃ Φ : JetR R (Fin n) M →ₐ[R] Jet R (Fin 2 × Fin n) M,
    (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R).comp Φ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M ∧
    (spMap (cpyU M 0) ≫ x M) * (spMap (cpyU M 1) ≫ x M) = spMap Φ ≫ x M ∧
    ∀ j, Φ (zR M j) - zz M ((0 : Fin 2), j) - zz M ((1 : Fin 2), j) ∈ Kp M 0 * Kp M 1 := by sorry
