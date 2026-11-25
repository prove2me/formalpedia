-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2c_twist_mul_first_argument_jet
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c.twist_mul_first_argument_jet
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:48:35.487056+00:00
-- url     : https://prove2.me/theorems/c08b5715-3849-4ffc-a52c-07fba197c724
-- title:
--   CInd Fr Fix2c: twist mul first argument jet
-- statement:
--   The CInd Fr Fix2c construction uses the twist mul first argument jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddFirstSecond.lean#L259-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddFirstSecond.lean#L259-L311

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp exp_zero)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c.twist_mul_first_argument_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) := by sorry
