-- Prove2me | Theorems.Thm_CubicSurface27_classification_of_minus_one_classes
-- name    : CubicSurface27.classification_of_minus_one_classes
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T13:51:55.552167+00:00
-- url     : https://prove2.me/theorems/dae36da4-675a-49fc-a773-f74376453437
-- title:
--   Classification of the $(-1)$-classes
-- statement:
--   Under the same hypotheses as the Cauchy–Schwarz bound — $a>0$, $b_i\ge0$ integers, $a^2-\sum_i b_i^2=-1$ and $3a-\sum_i b_i=1$ — the bound $a<3$ forces $a\in\{1,2\}$, and the only possibilities are the classes already found:
--
--   - $a=1$ and exactly two of the $b_i$ equal $1$ (the rest $0$): the pair-line $L-E_i-E_j$;
--   - $a=2$ and exactly five of the $b_i$ equal $1$ (the rest $0$): the five-point conic $2L-\sum_{k\ne i}E_k$.
--
--   This is the source's conclusion that "in these cases the only possibilities are the ones we have found", ruling out any further class of irreducible rational curve of self-intersection $-1$.
--
--   **Formalization Note.** The conclusion is an explicit disjunction of the two coordinate patterns, matching `lineClass` and `conicClass`.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part I, 'Counting lines', exhaustiveness: 'It is easy to see that in these cases the only possibilities are the ones we have found' (a = 1 or a = 2).

import Mathlib
open Finset

namespace CubicSurface27

theorem classification_of_minus_one_classes (a : ℤ) (b : Fin 6 → ℤ)
    (ha : 0 < a) (hb : ∀ i, 0 ≤ b i)
    (hself : a ^ 2 - ∑ i : Fin 6, (b i) ^ 2 = -1)
    (hadj : 3 * a - ∑ i : Fin 6, b i = 1) :
    (a = 1 ∧ ∃ i j : Fin 6, i ≠ j ∧ b = fun k => if k = i ∨ k = j then 1 else 0) ∨
    (a = 2 ∧ ∃ i : Fin 6, b = fun k => if k = i then 0 else 1) := by sorry

end CubicSurface27
