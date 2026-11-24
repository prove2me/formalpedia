-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetCopy_eq_PS
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetCopy_eq_PS
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:28.682427+00:00
-- url     : https://prove2.me/theorems/5173a7a8-f024-44dd-8c6d-8036c85913da
-- title:
--   Exp GF: jet Copy eq PS
-- statement:
--   The Exp GF construction uses the jet Copy eq PS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSEqJetMap.lean#L82-L91

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetCopy_eq_PS {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i =
      jetSubstPS (m := m) (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by sorry
