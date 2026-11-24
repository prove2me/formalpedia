-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqTan_one_of_tan
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.one_of_tan
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:23.025043+00:00
-- url     : https://prove2.me/theorems/6b86d2fd-a816-4edb-97cc-67d5bd97cbda
-- title:
--   Exp Uniq Tan: one of tan
-- statement:
--   The Exp Uniq Tan construction uses the one of tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqTan.lean#L156-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqTan.lean#L156-L185

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.one_of_tan {κ : Type} [Fintype κ] [DecidableEq κ] (δ : sp (R₀ := R) (Jet R κ (0 + 1)) ⟶ G)
    (hu : spMap (jetAug : Jet R κ (0 + 1) →ₐ[R] R) ≫ δ = 1)
    (ht : ∀ ℓ, spMap (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) ≫ δ = 1) : δ = 1 := by sorry
