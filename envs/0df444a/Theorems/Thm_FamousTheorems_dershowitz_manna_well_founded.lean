-- Prove2me | Theorems.Thm_FamousTheorems_dershowitz_manna_well_founded
-- name    : FamousTheorems.dershowitz_manna_well_founded
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:09.539992+00:00
-- url     : https://prove2.me/theorems/beda7d67-242d-4bf1-bdc9-efb4326626d5
-- title:
--   The Dershowitz–Manna ordering is well-founded
-- statement:
--   **Well-foundedness of the Dershowitz–Manna ordering.** If $<$ is a well-founded order on $\alpha$, then the Dershowitz–Manna multiset ordering on finite multisets over $\alpha$ is well-founded.
--
--   In this ordering $M<N$ when $M$ is obtained from $N$ by removing a nonempty sub-multiset $X$ and adding a multiset $Y$ each of whose elements is smaller than some element of $X$. Dershowitz and Manna introduced it in 1979 to prove termination of programs and term-rewriting systems. It is a standard tool in rewriting theory and underlies the multiset path ordering.
--
--   **Formalization note.** Mathlib's `Multiset.wellFounded_isDershowitzMannaLT`. `Multiset.IsDershowitzMannaLT M N` is the relation $M<N$ above, and `WellFoundedLT α` says that $<$ on the preorder $\alpha$ is well-founded.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Multiset.wellFounded_isDershowitzMannaLT`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dershowitz_manna_well_founded {α : Type*} [Preorder α] [WellFoundedLT α] :
    WellFounded (Multiset.IsDershowitzMannaLT : Multiset α → Multiset α → Prop) := by sorry

end FamousTheorems
