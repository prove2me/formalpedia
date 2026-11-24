-- Prove2me | Theorems.Thm_Formalism_SA_P_node_sub_node_ge
-- name    : Formalism.SA.P.node_sub_node_ge
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:56.079539+00:00
-- url     : https://prove2.me/theorems/c8684f74-adc5-43aa-b1cc-5f5387852535
-- title:
--   P: node sub node ge
-- statement:
--   The P construction uses the node sub node ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/ChebyshevLeadingCoeffHolds.lean#L8-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/ChebyshevLeadingCoeffHolds.lean#L8-L62

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Mathlib
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open Finset Real Polynomial Polynomial.Chebyshev

theorem Formalism.SA.P.node_sub_node_ge {n i k : ℕ} (hn : 1 ≤ n) (hik : i < k) (hk : k ≤ n) :
    2 * ((k:ℝ) - i) ^ 2 / (n:ℝ) ^ 2 ≤ node n i - node n k := by sorry
