-- Prove2me | Theorems.Thm_BiAbduction_Footprint_theorem_4_11
-- name    : BiAbduction.Footprint.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:58.784035+00:00
-- url     : https://prove2.me/theorems/7d58badb-0b44-4136-938b-f12ef0193dfd
-- title:
--   Theorem 4.11 (Deriving Footprint) — with precise preconditions and best anti-frames, foot(C) = P_C
-- statement:
--   Let $C = \alpha; C'$ be a nonempty sequence of actions, each action $\beta$ given by its specification $\{P_\beta\}\,\beta\,\{Q_\beta\}$, and suppose that every precondition $P_\beta$ of the sequence is precise. Let $P_C$ be the precondition of the canonical spec of $C$ obtained when every call to the bi-abductive prover delivers the best anti-frame: $P_\alpha$ for a single action, and $P_\alpha * M$ for $\alpha; C'$, where $M$ is the best solution of $Q_\alpha * M \models P_{C'} * \mathsf{true}$. Then
--   $$\mathrm{foot}(C) = P_C,$$
--   an equality of predicates, where $\mathrm{foot}(C) = \min(\mathrm{safe}(C))$ is the footprint of Definition 4.10.
--
--   The theorem says that, on straight-line paths, analysis by bi-abduction with an ideal prover infers exactly the footprint: the minimal states on which the sequence does not fault.
--
--   **Formalization Note** A sequence is a head action and a tail list. The canonical precondition is the inductive relation `IsCanonPre`, built from the proof of the theorem (the paper does not define the canonical spec in §4.2.4); its anti-frames are arbitrary ≾-least solutions, so the theorem is not an unfolding of a definition. Precision is assumed for every action of the sequence, including the last.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 50, Theorem 4.11

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics
import Definitions.Def_BiAbduction_Footprint_Footprint

namespace BiAbduction.Footprint

/-- Theorem 4.11 (Deriving Footprint, p. 50): if the precondition of every action of the sequence
`α; C` is precise and `P` is the precondition of the canonical spec of `α; C` obtained when
every bi-abduction call delivers the best anti-frame, then `foot(α; C) = P`. -/
theorem theorem_4_11 (α : Action) (C : List Action) (P : Pred)
    (hprec : ∀ a ∈ α :: C, IsPrecise a.pre) (hcanon : IsCanonPre α C P) :
    foot α C = P := by sorry

end BiAbduction.Footprint
