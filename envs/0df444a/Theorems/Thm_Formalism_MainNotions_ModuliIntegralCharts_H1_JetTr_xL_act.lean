-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_xL_act
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_act
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:04:00.431525+00:00
-- url     : https://prove2.me/theorems/af70ec06-6b0f-5e58-b7f9-a717a2a7c426
-- title:
--   Jet Tr: x L act
-- statement:
--   The Jet Tr construction uses the x L act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L124-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L124-L134

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_act (actT : Fin d → MvPowerSeries (Fin 1 × Fin d) T.V) (a : 𝓞 E) (m : ℕ) (ha : xT m ≫ I.G.act.act a =
      Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (actT p.2)) ≫ xT m) :
    xL I xT m ≫ (I.t'.act.act a).left =
      spMap ((jetSubstP m fun p : Fin 1 × Fin d => MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (actT p.2)) :
        Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
          Jet T.Fr (Fin 1 × Fin d) m →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT m := by sorry
