-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsTr_tau_proj
-- name    : Formalism.L2.SG.Pf.AllRowsTr.tau_proj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:32:27.785449+00:00
-- url     : https://prove2.me/theorems/1c13259e-012d-458c-9409-4ae38bcfa515
-- title:
--   All Rows Tr: tau proj
-- statement:
--   The All Rows Tr construction uses the tau proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L33-L38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsTr
open Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.SG.Pf.AllRowsTr.tau_proj (a e : MonoidAlgebra ℂ G) (ha : a * a = a) (hsa : conjA a = a) (he : e * e = e)
    (hc : ∀ y, e * y = y * e) (hse : conjA e = e) :
    (a * e).coeff 1 = ((∑ h : G, Complex.normSq ((a * e).coeff h) : ℝ) : ℂ) := by sorry
