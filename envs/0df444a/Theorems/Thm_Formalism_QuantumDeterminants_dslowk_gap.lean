-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_dslowk_gap
-- name    : Formalism.QuantumDeterminants.dslowk_gap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:38.590216+00:00
-- url     : https://prove2.me/theorems/1d5da9ae-d0ad-4810-a2bf-9a05d221d499
-- title:
--   Quantum Determinants: dslowk gap
-- statement:
--   The Quantum Determinants construction uses the dslowk gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSLowK.lean#L120-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSLowK.lean#L120-L148

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL

theorem Formalism.QuantumDeterminants.dslowk_gap {n : ℕ} {lam : Fin n → ℝ} {c : ℝ} (hanti : StrictAnti lam)
    (hint : ∀ x, ∃ m : ℤ, lam x - c = m) {a b : Fin n} (hab : a < b) :
    ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) ≤ lam a - lam b := by sorry
