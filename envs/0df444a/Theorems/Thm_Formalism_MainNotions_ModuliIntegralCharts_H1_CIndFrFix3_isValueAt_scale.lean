-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_isValueAt_scale
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.isValueAt_scale
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:59:13.370344+00:00
-- url     : https://prove2.me/theorems/4f184597-ee6e-448c-97e2-6114cfa5efb1
-- title:
--   CInd Fr Fix3: is Value At scale
-- statement:
--   The CInd Fr Fix3 construction uses the is Value At scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/EvalSinglePointId.lean#L246-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/EvalSinglePointId.lean#L246-L255

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.isValueAt_scale {a : ℤ} {T : Over Xo.X} {s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T)}
    {z : T ⟶ Xo.univ.t.G}
    {τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) fun _ => a)}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z τ v) (w : Γ(T.left, ⊤)ˣ) :
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z (scaleGen _ _ w τ) (v * ((w⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))) := by sorry
