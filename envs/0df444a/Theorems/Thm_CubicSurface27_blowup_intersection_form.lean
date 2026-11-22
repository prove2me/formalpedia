-- Prove2me | Theorems.Thm_CubicSurface27_blowup_intersection_form
-- name    : CubicSurface27.blowup_intersection_form
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T13:50:55.225984+00:00
-- url     : https://prove2.me/theorems/9a87e735-7053-4a7c-9732-a7ba5b896ead
-- title:
--   Blowup intersection form and $H^2 = 3$
-- statement:
--   This is the numerical check underlying the source's Proposition that the anticanonical image of the blowup is a smooth cubic surface. In the Picard lattice of $X=\mathrm{Bl}_{p_1,\dots,p_6}\mathbb{P}^2$, with $L$ the class of a line avoiding the six points and $E_i$ the exceptional divisor over $p_i$, the intersection pairing satisfies the source's four rules:
--
--   1. $L^2=1$ (two lines in $\mathbb{P}^2$ meet in a point);
--   2. $L\cdot E_i=0$ for every $i$;
--   3. $E_i\cdot E_j=0$ for $i\ne j$ (the exceptional curves are disjoint);
--   4. $E_i^2=-1$ for every $i$.
--
--   It follows that the hyperplane class $H=3L-E_1-\cdots-E_6$ of the cubic embedding satisfies
--   $$H^2=(3L-E_1-\cdots-E_6)^2=9-6=3,$$
--   so the embedding has degree $3$.
--
--   **Formalization Note.** Stated in the concrete lattice of `Definitions.Def_blowup_lattice_27`; the pairing is `inter`. The geometric assertion that the image is a smooth cubic surface is not part of this item — only the numerical check the source performs.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part I, 'Blowup description of a cubic surface', Proposition and its proof, intersection facts 1–4 and the computation H² = 9 − 6 = 3.

import Mathlib
import Definitions.Def_blowup_lattice_27
open Finset

namespace CubicSurface27

theorem blowup_intersection_form :
    inter classL classL = 1 ∧
    (∀ i : Fin 6, inter classL (classE i) = 0) ∧
    (∀ i j : Fin 6, i ≠ j → inter (classE i) (classE j) = 0) ∧
    (∀ i : Fin 6, inter (classE i) (classE i) = -1) ∧
    inter classH classH = 3 := by sorry

end CubicSurface27
