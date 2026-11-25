-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_exists_series
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_series
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:15.75815+00:00
-- url     : https://prove2.me/theorems/10a3ea32-31a4-4add-9468-f2cfe925218a
-- title:
--   Germ B: exists series
-- statement:
--   The Germ B construction uses the exists series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L151-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L151-L195

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_series {n : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    (φ : ∀ m, K → ((jOG x0 d m n).left ⟶ t.G.left)) (ε : K → ℤ)
    (φ' : ∀ m, K' → ((jOG x0 d m n).left ⟶ t.G.left)) (ε' : K' → ℤ)
    (A : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ m) ε)) (hA : ∀ m, (A m).IsGen)
    (B : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ' m) ε')) (hB : ∀ m, (B m).IsGen)
    (hF : ∀ m, FormEq (φ m) ε (φ' m) ε')
    (hAt : ∀ m y J, Good t.PP.L y J → val (A (m + 1)) (ρn x0 d n m).left y J = val (A m) (𝟙 _) y J)
    (hBt : ∀ m y J, Good t.PP.L y J → val (B (m + 1)) (ρn x0 d n m).left y J = val (B m) (𝟙 _) y J) :
    ∃ ph : MvPowerSeries (Fin n × Fin d) S, ∀ m, ∃ u : (Jet S (Fin n × Fin d) m)ˣ,
      (u : Jet S (Fin n × Fin d) m) = psJet m ph ∧
      LB.Gen.Corr t.PP.L _ _ _ _ (A m) (scaleGenG t _ _ (unitΓ u) (B m)) := by sorry
