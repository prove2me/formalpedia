-- Prove2me | solution 1 for mme_stothers_phi233_named_hash_fiber_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:24:55.219+00:00
-- url     : https://prove2.me/submissions/d37b1710-5d4d-4781-be55-ba3e8de89e20

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_retention_data
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_cyclic_edge_retention_card
import Theorems.Thm_mme_stothers_phi233_cyclic_pair_retention_card_le

open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (S : Finset (ZMod p))
    [DecidableEq (CyclicAmbientEdge N alpha beta gamma delta)]
    [DecidableEq (CyclicModeWord N)]
    [DecidableRel (Retained p N alpha beta gamma delta S)] :
    (∀ e ∈ targetFinset N alpha beta gamma delta,
      ((Finset.univ : Finset (HashState p N)).filter
        (fun q ↦ Retained p N alpha beta gamma delta S q e)).card =
          S.card * p ^ (6 * N)) ∧
    (∀ ef ∈ ((targetFinset N alpha beta gamma delta ×ˢ
        ambientFinset N alpha beta gamma delta).filter (fun ef ↦
          ef.1 ≠ ef.2 ∧ ∃ i : Fin 3,
            cyclicModeWord ef.1 i = cyclicModeWord ef.2 i)),
      ((Finset.univ : Finset (HashState p N)).filter
        (fun q ↦ Retained p N alpha beta gamma delta S q ef.1 ∧
          Retained p N alpha beta gamma delta S q ef.2)).card ≤
            p ^ (6 * N)) := by
  constructor
  · intro e _he
    unfold Retained stateHash stateWeights stateShift HashState HashIndex
    convert (mme_stothers_phi233_cyclic_edge_retention_card
      (p := p) (N := N) (alpha := alpha) (beta := beta)
      (gamma := gamma) (delta := delta) hp e S) using 1
    apply congrArg Finset.card
    congr
  · intro ef hef
    have hcollision := (Finset.mem_filter.mp hef).2
    rcases hcollision with ⟨hne, i, hi⟩
    unfold Retained stateHash stateWeights stateShift HashState HashIndex
    convert (mme_stothers_phi233_cyclic_pair_retention_card_le
      (p := p) (N := N) (alpha := alpha) (beta := beta)
      (gamma := gamma) (delta := delta) hp ef.1 ef.2 S hne i hi) using 1
    apply congrArg Finset.card
    congr
