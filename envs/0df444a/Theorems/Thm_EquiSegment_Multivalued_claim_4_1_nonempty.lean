-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_claim_4_1_nonempty
-- name    : EquiSegment.Multivalued.claim_4_1_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:18.252364+00:00
-- url     : https://prove2.me/theorems/b5927cfc-da0d-421b-add3-01e721320cd9
-- title:
--   Claim 4.1, consequence — every segment has a zero partition
-- statement:
--   Let $p$ be prime. Let $\varphi$ be continuous on the cylinder, negative on the bottom and positive on the top, and satisfy $\varphi([a,a],y)=y$ on degenerate segments. For every segment $I=[a,b]\subseteq[0,1]$, there is a value $y\in[-1,1]$ and a partition into exactly $p$ consecutive possibly degenerate segments on which $\varphi$ vanishes at $y$:
--
--   $$
--   \forall I\in\mathcal I,\quad\exists y\in[-1,1],\ a=x_0\le\cdots\le x_p=b,\quad
--   \varphi([x_{j-1},x_j],y)=0\ (1\le j\le p).
--   $$
--
--   This is the nonemptiness consequence drawn after Claim 4.1 for the fixed-segment solution set $S_I$.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 8, paragraph after Remark 4.2 (consequence of Claim 4.1)

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, consequence of Claim 4.1, p. 8. -/
theorem claim_4_1_nonempty (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ)
    (hp : p.Prime) (hφ : IsRep φ) (hdeg : DegId φ) :
    ∀ s ∈ Seg, ∃ y ∈ Set.Icc (-1 : ℝ) 1, IsZeroPartition φ p s y := by sorry

end EquiSegment.Multivalued
