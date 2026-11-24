-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_corr_scaled_left
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.corr_scaled_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:01:35.231888+00:00
-- url     : https://prove2.me/theorems/8980d22a-9db1-421a-8d9b-cc561f8f6f02
-- title:
--   Gauge R: corr scaled left
-- statement:
--   The Gauge R construction uses the corr scaled left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqA.lean#L103-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqA.lean#L103-L119

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {X Y Z : Scheme.{0}} (L : LB X)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.corr_scaled_left (hL : L.IsLB) (ψ : Y ⟶ X) (a : ℤ) {K' : Type} [Fintype K'] (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (τ τ' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U : Γ(Y, ⊤)ˣ) (h₂ : IsScaled U t₂ t₂')
    (c : LB.Gen.Corr L _ _ _ _ τ t₂) (c' : LB.Gen.Corr L _ _ _ _ τ' t₂') : IsScaled U τ τ' := by sorry
