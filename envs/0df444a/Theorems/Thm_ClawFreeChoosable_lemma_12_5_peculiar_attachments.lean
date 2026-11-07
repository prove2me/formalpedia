-- Prove2me | Theorems.Thm_ClawFreeChoosable_lemma_12_5_peculiar_attachments
-- name    : ClawFreeChoosable.lemma_12_5_peculiar_attachments
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:04.321492+00:00
-- url     : https://prove2.me/theorems/8b491feb-a49e-449e-b1be-6bceaac7a896
-- title:
--   Lemma 12.5 — attachments to peculiar graphs
-- statement:
--   A finite peculiar graph (Definition 12.4, the cliques $K_1, K_2, K_3$ possibly empty) is either cobipartite or has no nonempty attachable clique.
--
--   Hence a nonempty precoloured clique cannot be attached to a peculiar atom that is not cobipartite, which closes that case of the proof of Theorem 1.3.
--
--   Differences from the source: none.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Lemma 12.5, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsPeculiar
import Definitions.Def_ClawFreeChoosable_IsCobipartite
import Definitions.Def_ClawFreeChoosable_IsAttachable

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Lemma 12.5** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.33): a peculiar graph is either cobipartite or has no nonempty
attachable clique.

**Formalization Note.** "Peculiar" is Definition 12.4 as printed (`IsPeculiar`: the cliques
`K₁, K₂, K₃` may be empty), the more general hypothesis. -/
theorem lemma_12_5_peculiar_attachments {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : IsPeculiar G) :
    IsCobipartite G ∨ ∀ Q : Set V, Q.Nonempty → ¬ IsAttachable G Q := by sorry

end ClawFreeChoosable
