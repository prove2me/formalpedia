-- Prove2me | solution 1 for mme_CW_2376_augmented_hash_state_universe_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:15:27.487279+00:00
-- url     : https://prove2.me/submissions/4ed54335-03d9-4885-ada9-249df3d73904

import Definitions.Def_mme_CW_2376_hash_incidence_universes

open MME

set_option autoImplicit false

/-- The augmented parameter space has `p^(N+2)` states: `N+1` weights and
one affine offset. -/
theorem solution
    (m p : ℕ) [Fact p.Prime] :
    (cw2376AugmentedHashStateUniverse m p).card =
      p ^ (cw2376ProfileLength m + 2) := by
  classical
  simp only [cw2376AugmentedHashStateUniverse, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [show cw2376ProfileLength m + 2 =
      (cw2376ProfileLength m + 1) + 1 by omega]
  exact (pow_succ p (cw2376ProfileLength m + 1)).symm
