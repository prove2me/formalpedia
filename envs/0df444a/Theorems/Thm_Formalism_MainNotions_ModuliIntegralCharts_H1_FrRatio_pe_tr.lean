-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_pe_tr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.pe_tr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:39:10.073853+00:00
-- url     : https://prove2.me/theorems/451c3442-367c-47c2-9e01-6d4a1f058c4a
-- title:
--   Fr Ratio: pe tr
-- statement:
--   The Fr Ratio construction uses the pe tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L79-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L79-L91

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.pe_tr (e : ∀ m, FrTyG t x0 d x m) {n : ℕ} (m : ℕ) (v' v : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hv : ∀ i j, v' i j - v i j ∈ orig S (Fin n × Fin d) ^ (m + 1)) (y : (jOG x0 d m n).left)
    (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) v') (ρn x0 d n m).left y J =
      val (e (m + 1)) ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) y J := by sorry
