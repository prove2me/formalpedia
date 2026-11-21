-- Prove2me | Theorems.Thm_CubicSurface27_card_the27
-- name    : CubicSurface27.card_the27
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T13:52:21.237103+00:00
-- url     : https://prove2.me/theorems/95abf1b1-70f7-433c-8b5a-d562e081aaf5
-- title:
--   The $27$ classes are distinct: $6 + 15 + 6 = 27$
-- statement:
--   The three families comprise $6+15+6=27$ distinct classes: the six exceptional divisors $E_i$, the fifteen pair-lines $L-E_i-E_j$ (one for each unordered pair $\{i,j\}$), and the six five-point conics $2L-\sum_{k\ne i}E_k$. This item asserts that the finite set `the27` has cardinality $27$ — the source's "Thus we have found a total of 27 lines!"
--
--   **Formalization Note.** Distinctness is automatic from the coordinates: the three families have different $a$-values ($0$, $1$, $2$), and within each family the $b$-patterns are pairwise distinct.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part I, 'Counting lines': 6 exceptional divisors, 15 pair-lines, 6 conics; 'Thus we have found a total of 27 lines!'

import Mathlib
import Definitions.Def_blowup_lattice_27
open Finset

namespace CubicSurface27

theorem card_the27 : the27.card = 27 := by sorry

end CubicSurface27
