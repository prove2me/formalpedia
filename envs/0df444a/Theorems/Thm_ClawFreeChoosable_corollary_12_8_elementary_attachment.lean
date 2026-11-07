-- Prove2me | Theorems.Thm_ClawFreeChoosable_corollary_12_8_elementary_attachment
-- name    : ClawFreeChoosable.corollary_12_8_elementary_attachment
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:30.319488+00:00
-- url     : https://prove2.me/theorems/9b4b6767-9487-4485-929b-74c7cf9f7827
-- title:
--   Corollary 12.8 — attachments to elementary atoms
-- statement:
--   Let $G$ be a finite connected claw-free graph, let $S \ne \emptyset$ be a clique of simplicial vertices of $G$, and suppose that $G - S$ is an elementary atom that is not cobipartite. Then $G$ is elementary.
--
--   This lets the elementary precolouring-extension theorem (Theorem 10.5) be applied to $G$ itself in the last case of the proof of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: G − S → G.induce Sᶜ; reason: Lean convention; same instances
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Corollary 12.8, p.37 (PDF p.40)

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsClawFree
import Definitions.Def_ClawFreeChoosable_IsSimplicialClique
import Definitions.Def_ClawFreeChoosable_IsElementary
import Definitions.Def_ClawFreeChoosable_IsAtom
import Definitions.Def_ClawFreeChoosable_IsCobipartite

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Corollary 12.8 (Attachments to elementary atoms)** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.37). Let `G` be connected and
claw-free, let `S ≠ ∅` be a clique of simplicial vertices, and suppose `G − S` is an elementary
atom that is not cobipartite. Then `G` is elementary.

**Formalization Note.** `G − S` is `G.induce Sᶜ`. -/
theorem corollary_12_8_elementary_attachment {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hclaw : IsClawFree G) (S : Set V) (hSne : S.Nonempty)
    (hS : IsSimplicialClique G S) (helem : IsElementary (G.induce Sᶜ))
    (hatom : IsAtom (G.induce Sᶜ)) (hcob : ¬ IsCobipartite (G.induce Sᶜ)) :
    IsElementary G := by sorry

end ClawFreeChoosable
