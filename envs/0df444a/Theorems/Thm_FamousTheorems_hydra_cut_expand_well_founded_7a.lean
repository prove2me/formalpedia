-- Prove2me | Theorems.Thm_FamousTheorems_hydra_cut_expand_well_founded_7a
-- name    : FamousTheorems.hydra_cut_expand_well_founded_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:55.493274+00:00
-- url     : https://prove2.me/theorems/7fa1c9ae-2151-4274-834a-7e0f7b9c487e
-- title:
--   Termination of the hydra game (Kirby–Paris): CutExpand is well-founded
-- statement:
--   **Termination of the hydra game.** Let $r$ be a well-founded relation on $\alpha$. Then the relation $\mathrm{CutExpand}(r)$ on finite multisets of elements of $\alpha$ is well-founded. Here $\mathrm{CutExpand}(r)$ relates $t$ to $s$ when $t$ is obtained from $s$ by removing one element $a$ and adding finitely many elements $b$ with $r(b,a)$.
--
--   In the hydra game of Kirby and Paris (1982), Hercules cuts off a head of a finite tree and the hydra regrows finitely many copies of part of the tree. The theorem gives the essential step of the proof that Hercules always wins. Kirby and Paris showed that this cannot be proved in Peano arithmetic. The transitive closure of this relation is the Dershowitz–Manna multiset ordering induced by $r$, which is used to prove termination of rewriting systems.
--
--   **Formalization note.** Mathlib's `WellFounded.cutExpand`. `Relation.CutExpand r` is defined on `Multiset α`. In Mathlib the relation `CutExpand r s' s` holds when $s'$ is obtained from $s$ by replacing one element $a$ by a finite multiset of elements that are $r$-smaller than $a$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `WellFounded.cutExpand`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hydra_cut_expand_well_founded_7a {α : Type*} {r : α → α → Prop} (hr : WellFounded r) : WellFounded (Relation.CutExpand r) := by sorry

end FamousTheorems
