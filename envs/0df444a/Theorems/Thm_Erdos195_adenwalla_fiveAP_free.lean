-- Prove2me | Theorems.Thm_Erdos195_adenwalla_fiveAP_free
-- name    : Erdos195.adenwalla_fiveAP_free
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:33:14.706996+00:00
-- url     : https://prove2.me/theorems/64154951-da85-4e04-95ac-c66c24415a84
-- title:
--   Adenwalla: a permutation of $\mathbb{Z}$ with no monotone $5$-term AP
-- statement:
--   There is a bijection $f:\mathbb{N}\to\mathbb{Z}$ with no monotone $5$-term arithmetic progression.
--
--   $$\exists f:\mathbb{N}\simeq\mathbb{Z}\ \text{ with no } i_1<\dots<i_5 \text{ such that } f(i_1),\dots,f(i_5) \text{ is an increasing or decreasing AP.}$$
--
--   This is the upper bound $K\le4$ in Erdős Problem 195.
--
--   **Formalization Note** Permutations are `f : ℕ ≃ ℤ`; `HasMonotoneAP` is copied verbatim from formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`): a list of indices `l` with `l.Pairwise (· < ·)` whose image is an arithmetic progression of length $k$, listed forwards or backwards.
-- source:
--   S. Adenwalla, Avoiding monotone arithmetic progressions in permutations of integers, Discrete Math. 347 (2024) 114183, arXiv:2211.04451, Theorem 1

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem adenwalla_fiveAP_free : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 5 := by sorry

end Erdos195
