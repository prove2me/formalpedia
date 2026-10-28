-- Prove2me | Theorems.Thm_Erdos195_degs_three_ap
-- name    : Erdos195.degs_three_ap
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:32:47.021986+00:00
-- url     : https://prove2.me/theorems/be899e98-a340-4582-b579-11f9700d0ee4
-- title:
--   Every permutation of $\mathbb{Z}$ contains a monotone $3$-term AP
-- statement:
--   Every bijection $f:\mathbb{N}\to\mathbb{Z}$ has a monotone $3$-term arithmetic progression: there are indices $i<j<l$ such that $f(i),f(j),f(l)$ is an increasing or decreasing AP.
--
--   $$\forall f:\mathbb{N}\simeq\mathbb{Z},\quad \exists\, i<j<l:\ f(j)-f(i)=f(l)-f(j).$$
--
--   This is the lower bound $K\ge3$ in Erdős Problem 195. It follows from the theorem of Davis, Entringer, Graham and Simmons that every permutation of the positive integers contains a monotone $3$-AP, applied to the positive entries of $f$.
--
--   **Formalization Note** Permutations are `f : ℕ ≃ ℤ`; `HasMonotoneAP` is copied verbatim from formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`): a list of indices `l` with `l.Pairwise (· < ·)` whose image is an arithmetic progression of length $k$, listed forwards or backwards.
-- source:
--   J. A. Davis, R. C. Entringer, R. L. Graham, G. J. Simmons, On permutations containing no long arithmetic progressions, Acta Arith. 34 (1977) 81–90, https://doi.org/10.4064/aa-34-1-81-90 ; restated in Adenwalla arXiv:2211.04451 §1

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem degs_three_ap (f : ℕ ≃ ℤ) : HasMonotoneAP f 3 := by sorry

end Erdos195
