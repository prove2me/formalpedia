-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_thmPExp_degree_le_of_mem_antidiagonal
-- name    : Formalism.IncomingBounds.thmPExp_degree_le_of_mem_antidiagonal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:21.353781+00:00
-- url     : https://prove2.me/theorems/b8de055f-06e6-45d0-b112-e21c0034f00c
-- title:
--   Incoming Bounds: thm PExp degree le of mem antidiagonal
-- statement:
--   The Incoming Bounds construction uses the thm PExp degree le of mem antidiagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L40-L45

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}

theorem Formalism.IncomingBounds.thmPExp_degree_le_of_mem_antidiagonal [DecidableEq σ] {m : σ →₀ ℕ} {pq : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hpq : pq ∈ antidiagonal m) : pq.1.degree ≤ m.degree ∧ pq.2.degree ≤ m.degree := by sorry
