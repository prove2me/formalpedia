-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_prod_finPairsLT
-- name    : Formalism.ResultantValuation.LaplaceProof.prod_finPairsLT
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:46.293965+00:00
-- url     : https://prove2.me/theorems/9c58d095-702c-4dc1-a2d4-e353ab259d39
-- title:
--   Laplace Proof: prod fin Pairs LT
-- statement:
--   The Laplace Proof construction uses the prod fin Pairs LT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L17-L24

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof

theorem Formalism.ResultantValuation.LaplaceProof.prod_finPairsLT {n : ℕ} (f : (Σ _ : Fin n, Fin n) → ℤˣ) :
    ∏ p ∈ Perm.finPairsLT n, f p = ∏ x : Fin n, ∏ y : Fin n, if y < x then f ⟨x, y⟩ else 1 := by sorry
