-- Prove2me | Theorems.Thm_BiAbduction_Footprint_safe_eq_foot_sep_true
-- name    : BiAbduction.Footprint.safe_eq_foot_sep_true
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:54.400991+00:00
-- url     : https://prove2.me/theorems/12ddfb07-733d-4935-8b5e-8afa20db71fa
-- title:
--   Proof of Thm 4.11 — the safe states are the footprint ∗ true: safe(C) = foot(C) ∗ true
-- statement:
--   Let $C$ be a nonempty sequence of actions, each given by a pair of arbitrary predicates $(P_\alpha, Q_\alpha)$, with safe states $\mathrm{safe}(C)$ and footprint $\mathrm{foot}(C) = \min(\mathrm{safe}(C))$ as in Definition 4.10. Then
--   $$\mathrm{safe}(C) = \mathrm{foot}(C) * \mathsf{true}.$$
--
--   This is the content of the step "foot(C) = $P_C$, and therefore safe(C) = $P_C$ ∗ true" in the proof of Theorem 4.11: once the footprint is known, the safe states are exactly the states that extend a footprint state by separate memory.
--
--   **Formalization Note** No precision hypothesis is needed for this identity, and none is assumed.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 50, §4.2.4, proof of Theorem 4.11

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics
import Definitions.Def_BiAbduction_Footprint_Footprint

namespace BiAbduction.Footprint

/-- Proof of Theorem 4.11 (p. 50), "foot(C) = P_C, and therefore safe(C) = P_C ∗ true":
for every nonempty sequence of actions, the safe states are the footprint extended by an
arbitrary separate heap, `safe(C) = foot(C) ∗ true`. -/
theorem safe_eq_foot_sep_true (α : Action) (C : List Action) :
    safe α C = sepConj (foot α C) Set.univ := by sorry

end BiAbduction.Footprint
