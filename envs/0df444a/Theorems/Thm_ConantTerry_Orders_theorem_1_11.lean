-- Prove2me | Theorems.Thm_ConantTerry_Orders_theorem_1_11
-- name    : ConantTerry.Orders.theorem_1_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:35.180382+00:00
-- url     : https://prove2.me/theorems/0831dbe9-403f-49d3-857b-60142af32ac6
-- title:
--   Theorem 1.11 — extracting non-uniform ladders from trees
-- statement:
--   Let $X,Y$ be arbitrary sets and $f:X\times Y\to[0,1]$. For every integer $k\ge1$ and every real $\delta>0$,
--   $$
--   \operatorname{AdmitsTree}\!\left(f,\binom{2k}{k}-1,2\delta\right)
--   \quad\Longrightarrow\quad
--   \operatorname{AdmitsLadder}(f,k,\delta).
--   $$
--   A tree uses thresholds in $[0,1]$ at its internal binary-word nodes and tests every pair of opposite-branch leaves. The ladder has its high entries on and above the diagonal, its low entries below it, and independently varying thresholds in $[0,1]$ for each row. Neither ambient set is assumed finite or nonempty. There is no uniformity assumption, Boolean-valued restriction, additional slack or loss in the stated height.
--
--   This is the first main result of the pinned submission. It provides the non-uniform extraction bound used in the source's subsequent results on uniform ladders, dual sequential fat-shattering and quantitative stable regularity.
--
--   Differences from the source:
--   - encoding: binary words in B_<t, B_≤t and B_t → length-constrained subtypes of List Bool, with false = 0 and true = 1; reason: the empty word, concatenation and initial-segment order are preserved exactly
--   - encoding: [n] = {1,...,n} → Fin n = {0,...,n-1}; reason: subtracting one from every index preserves the order and all diagonal conventions
--   - encoding: f and thresholds take values in [0,1] → f and thresholds take values in the real subtype Set.Icc 0 1; reason: subtype membership enforces precisely the source range without added regularity assumptions
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.5, Theorem 1.11; Section 3, proof pp.10–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_ladder

namespace ConantTerry.Orders

/-- Theorem 1.11, p.5, proved in Section 3, pp.10–12.
Arbitrary ambient types, positive real scale, exact central binomial height,
and row-dependent thresholds; no uniformity or slack assumption. -/
theorem theorem_1_11 {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k)
    (δ : ℝ) (hδ : 0 < δ)
    (hTree : AdmitsTree f (Nat.choose (2 * k) k - 1) (2 * δ)) :
    AdmitsLadder f k δ := by sorry

end ConantTerry.Orders
