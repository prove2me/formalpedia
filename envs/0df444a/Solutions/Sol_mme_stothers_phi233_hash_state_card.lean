-- Prove2me | solution 1 for mme_stothers_phi233_hash_state_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:16:37.305341+00:00
-- url     : https://prove2.me/submissions/52c122ab-f39a-4760-aa31-5da5da4eb09f

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_state_instances

open MME

set_option autoImplicit false
set_option warningAsError true

/-- The Phi233 affine hash state space factors as `p^2` times the common
one-edge/pair fiber scale `p^(6N)`. -/
theorem solution (p N : ℕ) [Fact p.Prime] :
    Fintype.card (MME.StothersFourth.Phi233.HashState p N) =
      p ^ 2 * p ^ (6 * N) := by
  change Fintype.card
      ((((Fin 3 × Fin (2 * N)) ⊕ Unit) → ZMod p) × ZMod p) = _
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
    Fintype.card_prod, ZMod.card]
  simp only [Fintype.card_fin, Fintype.card_unit]
  rw [show 3 * (2 * N) + 1 = 6 * N + 1 by omega]
  rw [pow_succ]
  ring
