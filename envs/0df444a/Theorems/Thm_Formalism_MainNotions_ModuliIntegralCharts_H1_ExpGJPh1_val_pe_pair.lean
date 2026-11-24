-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh1_val_pe_pair
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.val_pe_pair
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:06.937764+00:00
-- url     : https://prove2.me/theorems/5446b05d-32ba-424c-9def-c2655a16d868
-- title:
--   Exp GJPh1: val pe pair
-- statement:
--   The Exp GJPh1 construction uses the val pe pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SubstCoeRename.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SubstCoeRename.lean#L40-L54

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SubstCoeRename
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.val_pe_pair (C : ChartAt Xo c y) (m : ℕ) (P3 : Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP3c : ∀ i j, MvPowerSeries.constantCoeff (P3 i j) = 0)
    (σ : Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) (hσ : ∀ i j, MvPolynomial.constantCoeff (σ i j) = 0)
    (Q : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hQ : ∀ i j, MvPowerSeries.constantCoeff (Q i j) = 0)
    (hs : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
      ((σ i j : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) = psJet m (Q i j))
    {z : (jO y (dL Dw) m 1).left} {J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι}
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (pe y C.d C.x C.e m σ) (ptm C P3 m).left z J = val (C.e m) (ptm C Q m).left z J := by sorry
