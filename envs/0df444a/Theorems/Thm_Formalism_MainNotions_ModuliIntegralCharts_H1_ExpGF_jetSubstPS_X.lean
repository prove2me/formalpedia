-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_X
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstPS_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:17:40.341925+00:00
-- url     : https://prove2.me/theorems/79f6f43e-70ec-49bb-b763-4ca351a3b79a
-- title:
--   Exp GF: jet Subst PS X
-- statement:
--   The Exp GF construction uses the jet Subst PS X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L20-L24

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstPS_X (m : ℕ) (P : κ → MvPowerSeries κ' S) (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (i : κ) : jetSubstPS (m := m) P (Ideal.Quotient.mk _ (X i)) = psJet m (P i) := by sorry
