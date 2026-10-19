-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_lemma_2_2_b
-- name    : EquiSegment.Multivalued.lemma_2_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:17.999586+00:00
-- url     : https://prove2.me/theorems/65278fc0-5ee2-4536-a185-b58d2b86f05a
-- title:
--   Lemma 2.2(b) — a representation has a nice zero set
-- statement:
--   Let $\varphi$ be a continuous real function on the cylinder $C=\mathcal I\times[-1,1]$, negative on its bottom and positive on its top. Then its zero graph is compact, lies strictly between the two ends of the cylinder, and separates the top from the bottom:
--
--   $$
--   Z(\varphi)=\{(I,y)\in C:\varphi(I,y)=0\}\quad\text{is nice}.
--   $$
--
--   This is the passage from an ordinary function to the paper's nice multivalued function.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 2, Lemma 2.2(b)

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, Lemma 2.2(b), p. 2. -/
theorem lemma_2_2_b (φ : ℝ × ℝ → ℝ → ℝ) (hφ : IsRep φ) :
    IsNice (zeroSet φ) := by sorry

end EquiSegment.Multivalued
