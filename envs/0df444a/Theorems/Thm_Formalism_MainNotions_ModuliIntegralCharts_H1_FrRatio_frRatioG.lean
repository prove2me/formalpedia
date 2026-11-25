-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_frRatioG
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.frRatioG
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:41:04.1229+00:00
-- url     : https://prove2.me/theorems/818ceb9c-09a8-44fe-99e7-52590f1709c7
-- title:
--   Fr Ratio: fr Ratio G
-- statement:
--   The Fr Ratio construction uses the fr Ratio G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L157-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L157-L250

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
set_option maxHeartbeats 4000000

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.frRatioG (hch : IsChartG t x0 d F act tg uvec x) {ph1 ph2 sy ad} {e : ∀ m, FrTyG t x0 d x m}
    (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) (m : ℕ) :
    ∃ U : (Jet S (Fin 2 × Fin d) m)ˣ,
      LB.Gen.Corr t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ (e (m + 1)) (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left)
        (scaleGenG t _ _ (unitΓ U) (e m)) ∧
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) * jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) ∧
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = U ∧
      ∀ a : 𝓞 E, jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) := by sorry
