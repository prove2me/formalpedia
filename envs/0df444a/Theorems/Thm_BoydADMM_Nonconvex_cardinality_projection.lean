-- Prove2me | Theorems.Thm_BoydADMM_Nonconvex_cardinality_projection
-- name    : BoydADMM.Nonconvex.cardinality_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:06:31.978333+00:00
-- url     : https://prove2.me/theorems/810d772f-0935-4b36-b362-dba6503e512a
-- title:
--   §9.1 — projection onto a cardinality-constrained set
-- statement:
--   Let $v\in\mathbb R^n$ and $c\ge0$. Choose an index set $I$ of size $\min(c,n)$ such that $|v_i|\ge|v_j|$ whenever $i\in I$ and $j\notin I$. Let $w_i=v_i$ on $I$ and $w_i=0$ elsewhere. Then $w$ has at most $c$ nonzero entries and
--
--   $$\|w-v\|_2^2\le\|x-v\|_2^2\quad\text{for every }x\text{ with }\operatorname{card}(x)\le c.$$
--
--   Thus keeping any $c$ largest-magnitude coordinates gives a Euclidean projection onto the sparsity set.
--
--   **Formalization Note** When $c>n$, all $n$ coordinates are retained. Tied magnitudes can produce several nearest points; this theorem accepts every eligible $I$ and asserts nearest-point status, not uniqueness.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 74, §9.1, Cardinality bullet

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_ProjectionBasics

namespace BoydADMM.Nonconvex

/-- §9.1, p. 74: any choice of the `min c n` largest-magnitude coordinates
gives a nearest point of the cardinality-constrained set. -/
theorem cardinality_projection {n : ℕ} (v : Fin n → ℝ) (c : ℕ)
    (I : Finset (Fin n))
    (hcard : I.card = min c n)
    (hlargest : ∀ i ∈ I, ∀ j ∉ I, |v j| ≤ |v i|) :
    restrictTo I v ∈ sparseSet c ∧
    ∀ x ∈ sparseSet c, sqDist (restrictTo I v) v ≤ sqDist x v := by sorry

end BoydADMM.Nonconvex
