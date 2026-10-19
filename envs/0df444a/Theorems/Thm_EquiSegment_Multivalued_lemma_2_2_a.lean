-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_lemma_2_2_a
-- name    : EquiSegment.Multivalued.lemma_2_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:18.540041+00:00
-- url     : https://prove2.me/theorems/f8aaf759-1d80-4917-acf6-a1c770a63189
-- title:
--   Lemma 2.2(a) — every nice graph has a representation
-- statement:
--   Let $Z\subseteq\mathcal I\times(-1,1)$ be compact and separate the top of $\mathcal I\times[-1,1]$ from its bottom. There is a continuous real function $\varphi$ on the cylinder, negative on the bottom and positive on the top, whose entire zero graph is $Z$:
--
--   $$
--   \exists\varphi,\qquad Z=\{(I,y)\in\mathcal I\times[-1,1]:\varphi(I,y)=0\}.
--   $$
--
--   This representation lets subsequent statements work with a function while retaining the given graph exactly.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 2, Lemma 2.2(a)

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, Lemma 2.2(a), p. 2. -/
theorem lemma_2_2_a (Z : Set ((ℝ × ℝ) × ℝ)) (hZ : IsNice Z) :
    ∃ φ : ℝ × ℝ → ℝ → ℝ, IsRep φ ∧ zeroSet φ = Z := by sorry

end EquiSegment.Multivalued
