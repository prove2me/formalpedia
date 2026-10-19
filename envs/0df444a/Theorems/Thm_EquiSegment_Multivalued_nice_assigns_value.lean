-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_nice_assigns_value
-- name    : EquiSegment.Multivalued.nice_assigns_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:30.763982+00:00
-- url     : https://prove2.me/theorems/f53bd4af-95a2-4bae-9fdd-0e899330cebf
-- title:
--   Proof of Theorem 1.1 — a nice graph has a value on every segment
-- statement:
--   Let $Z$ be the compact graph of a nice multivalued function on the space $\mathcal I$ of segments $[a,b]\subseteq[0,1]$. Every segment occurs in that graph at some value strictly between the cylinder's ends:
--
--   $$
--   \forall I\in\mathcal I,\quad\exists y\in(-1,1),\quad(I,y)\in Z.
--   $$
--
--   This supplies a value on the full segment when the prime-factor reductions are complete.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 3, proof of Theorem 1.1, “From the definition it follows…”

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, proof of Theorem 1.1, p. 3. -/
theorem nice_assigns_value (Z : Set ((ℝ × ℝ) × ℝ)) (hZ : IsNice Z) :
    ∀ s ∈ Seg, ∃ y ∈ Set.Ioo (-1 : ℝ) 1, (s, y) ∈ Z := by sorry

end EquiSegment.Multivalued
