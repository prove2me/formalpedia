-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_xL_zero
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:04:58.703529+00:00
-- url     : https://prove2.me/theorems/9acf5e88-edf3-51bc-9692-5221c0b5d941
-- title:
--   Jet Tr: x L zero
-- statement:
--   The Jet Tr construction uses the x L zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L102-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L102-L112

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_zero (hz : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetAug : Jet T.V (Fin 1 × Fin d) m →ₐ[T.V] T.V) ≫ xT m = 1)
    (m : ℕ) : spMap ((jetAug : Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] T.Fr) : Jet T.Fr (Fin 1 × Fin d) m →+* T.Fr) ≫
      xL I xT m = η[I.t'.G].left := by sorry
