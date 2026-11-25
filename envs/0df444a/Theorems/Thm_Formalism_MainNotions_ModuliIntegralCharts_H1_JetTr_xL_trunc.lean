-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_xL_trunc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_trunc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:02:28.346665+00:00
-- url     : https://prove2.me/theorems/2afbb07b-d7ba-52d2-9779-423d5f39c12b
-- title:
--   Jet Tr: x L trunc
-- statement:
--   The Jet Tr construction uses the x L trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L114-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L114-L122

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_trunc (ht : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
      (jetTrunc : Jet T.V (Fin 1 × Fin d) (m + 1) →ₐ[T.V] Jet T.V (Fin 1 × Fin d) m) ≫ xT (m + 1) = xT m)
    (m : ℕ) : spMap ((jetTrunc : Jet T.Fr (Fin 1 × Fin d) (m + 1) →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
      Jet T.Fr (Fin 1 × Fin d) (m + 1) →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT (m + 1) = xL I xT m := by sorry
