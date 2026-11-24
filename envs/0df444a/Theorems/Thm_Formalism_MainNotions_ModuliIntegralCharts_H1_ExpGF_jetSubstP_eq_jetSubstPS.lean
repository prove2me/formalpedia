-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstP_eq_jetSubstPS
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstP_eq_jetSubstPS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:57.743697+00:00
-- url     : https://prove2.me/theorems/f7c8eb13-d14c-48bf-84b9-ee8f5a797e98
-- title:
--   Exp GF: jet Subst P eq jet Subst PS
-- statement:
--   The Exp GF construction uses the jet Subst P eq jet Subst PS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L68-L80

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstP_eq_jetSubstPS (m : ℕ) (σ : κ → MvPolynomial κ' S) (hσ : ∀ i, MvPolynomial.constantCoeff (σ i) = 0) :
    jetSubstP m σ = jetSubstPS (m := m) (fun i => (σ i : MvPowerSeries κ' S)) := by sorry
