-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_eq_jetMap
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstPS_eq_jetMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:35.122898+00:00
-- url     : https://prove2.me/theorems/447bfd85-e222-4230-91c8-99567d24b9ff
-- title:
--   Exp GF: jet Subst PS eq jet Map
-- statement:
--   The Exp GF construction uses the jet Subst PS eq jet Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L26-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L26-L46

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstPS_eq_jetMap (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    jetSubstPS (m := m) Q = jetMap (fun i => psTrunc m (Q i)) (fun i => psTrunc_mem_orig m (Q i) (hQ i)) := by sorry
