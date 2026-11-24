-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_comp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstPS_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:17:16.6894+00:00
-- url     : https://prove2.me/theorems/394c03a4-e126-4ecd-8ca2-92d54c2c75dd
-- title:
--   Exp GF: jet Subst PS comp
-- statement:
--   The Exp GF construction uses the jet Subst PS comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L57-L66

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
variable {S : Type} [CommRing S] {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstPS_comp (m : ℕ) (P : κ → MvPowerSeries κ' S) (Q : κ' → MvPowerSeries κ'' S)
    (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    (jetSubstPS (m := m) Q).comp (jetSubstPS (m := m) P) =
      jetSubstPS (m := m) (fun i => MvPowerSeries.subst Q (P i)) := by sorry
