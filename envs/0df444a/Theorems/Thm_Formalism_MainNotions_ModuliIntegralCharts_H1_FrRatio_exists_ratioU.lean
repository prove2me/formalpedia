-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_exists_ratioU
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.exists_ratioU
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:29.261864+00:00
-- url     : https://prove2.me/theorems/d71765f4-3cf8-445e-b6cd-b4aa2febadba
-- title:
--   Fr Ratio: exists ratio U
-- statement:
--   The Fr Ratio construction uses the exists ratio U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L137-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L137-L154

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.exists_ratioU (hch : IsChartG t x0 d F act tg uvec x) (e : ∀ m, FrTyG t x0 d x m) (he : ∀ m, (e m).IsGen)
    (m : ℕ) : ∃ U : (Jet S (Fin 2 × Fin d) m)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 2).left) (z : Z)
      (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val (e (m + 1)) (r ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) z J =
        gm r z ⊤ (unitΓ U) * val (e m) r z J := by sorry
