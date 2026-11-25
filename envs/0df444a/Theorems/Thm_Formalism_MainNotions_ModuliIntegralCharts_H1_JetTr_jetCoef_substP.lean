-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_jetCoef_substP
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.jetCoef_substP
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:06:37.207316+00:00
-- url     : https://prove2.me/theorems/4737426f-edb7-4600-a142-1b800aa44bd5
-- title:
--   Jet Tr: jet Coef subst P
-- statement:
--   The Jet Tr construction uses the jet Coef subst P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L34-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrC.lean#L34-L64

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.jetCoef_substP {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) {κ κ' : Type} (m : ℕ)
    (φ : κ → MvPolynomial κ' V) :
    (jetCoef f κ' m).comp ((jetSubstP m φ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetSubstP m (fun i => MvPolynomial.map f (φ i)) : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by sorry
