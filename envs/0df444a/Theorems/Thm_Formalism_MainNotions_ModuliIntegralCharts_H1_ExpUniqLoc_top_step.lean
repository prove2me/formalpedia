-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_top_step
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.top_step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:00:08.621324+00:00
-- url     : https://prove2.me/theorems/b5d47ca0-68d5-4685-901d-9ab610066de5
-- title:
--   Exp Uniq Loc: top step
-- statement:
--   The Exp Uniq Loc construction uses the top step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqLoc.lean#L166-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqLoc.lean#L166-L238

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.top_step [Algebra ℚ R] {d M : ℕ} (hM : 2 ≤ M) (ψ : JetR R (Fin n) M →ₐ[R] Jet R (Fin 1 × Fin d) M)
    (hψa : (jetAug : Jet R (Fin 1 × Fin d) M →ₐ[R] R).comp ψ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M)
    (hψ : ∀ j, ψ (zR M j) ∈ Ij R (Fin 1 × Fin d) M ^ M)
    (hhom : spMap (sumJ d M) ≫ (spMap ψ ≫ x M) =
      (spMap (cpy d M 0) ≫ spMap ψ ≫ x M) * (spMap (cpy d M 1) ≫ spMap ψ ≫ x M)) :
    ∀ j, ψ (zR M j) = 0 := by sorry
