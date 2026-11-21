-- Prove2me | Theorems.Thm_CubicSurface27_minus_one_classes
-- name    : CubicSurface27.minus_one_classes
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T13:51:29.436733+00:00
-- url     : https://prove2.me/theorems/4109709b-f8fa-43b0-95fe-21cf5ef3ec62
-- title:
--   The three families are $(-1)$-classes
-- statement:
--   The source exhibits $27$ rational curves of self-intersection $-1$ on the blowup, whose images on the cubic surface are lines. They fall into three families, each of self-intersection $-1$:
--
--   1. the six exceptional divisors $E_i$, with $E_i^2=-1$;
--   2. for each unordered pair $\{i,j\}$, the class $L-E_i-E_j$ of the line through $p_i$ and $p_j$, with $(L-E_i-E_j)^2=1-2=-1$ — giving $\binom{6}{2}=15$ classes;
--   3. for each $i$, the class $2L-\sum_{k\ne i}E_k$ of the conic through the five points other than $p_i$, with $(2L-\sum_{k\ne i}E_k)^2=4-5=-1$ — giving $6$ classes.
--
--   This item asserts that every class in the three families has self-intersection $-1$.
--
--   **Formalization Note.** Self-intersection is `inter D D` in the concrete lattice; the three families are `classE`, `lineClass`, and `conicClass`.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part I, 'Counting lines', items 1–3 (the three families and their self-intersections).

import Mathlib
import Definitions.Def_blowup_lattice_27
open Finset

namespace CubicSurface27

theorem minus_one_classes :
    (∀ i : Fin 6, inter (classE i) (classE i) = -1) ∧
    (∀ i j : Fin 6, i ≠ j → inter (lineClass i j) (lineClass i j) = -1) ∧
    (∀ i : Fin 6, inter (conicClass i) (conicClass i) = -1) := by sorry

end CubicSurface27
