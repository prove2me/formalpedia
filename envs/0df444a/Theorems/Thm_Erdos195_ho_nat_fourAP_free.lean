-- Prove2me | Theorems.Thm_Erdos195_ho_nat_fourAP_free
-- name    : Erdos195.ho_nat_fourAP_free
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:34:33.833984+00:00
-- url     : https://prove2.me/theorems/57b1fdb5-ff3d-401f-a98e-7a909c7fa509
-- title:
--   Ho: a permutation of $\mathbb{N}$ with no monotone $4$-term AP
-- statement:
--   There is a bijection $f:\mathbb{N}\to\mathbb{N}$ with no monotone $4$-term arithmetic progression: no indices $i_1<i_2<i_3<i_4$ for which $f(i_1),\dots,f(i_4)$, viewed as integers, form an increasing or decreasing AP.
--
--   $$\exists f:\mathbb{N}\simeq\mathbb{N}\ \text{ with no monotone } 4\text{-AP}.$$
--
--   This resolves Erdős Problem 196 (the analogue for $\mathbb{N}$). Here $\mathbb{N}$ includes $0$; this is equivalent to Ho's statement for the positive integers by the shift $n\mapsto n+1$.
--
--   **Formalization Note** Permutations are `f : ℕ ≃ ℤ`; `HasMonotoneAP` is copied verbatim from formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`): a list of indices `l` with `l.Pairwise (· < ·)` whose image is an arithmetic progression of length $k$, listed forwards or backwards.
-- source:
--   B. S. Ho, A 4AP-free permutation of the positive integers, arXiv:2609.12780 (2026), Theorem; Lean proof github.com/boonsuan/4ap (FourAP.exists_fourAPFree_permutation)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem ho_nat_fourAP_free : ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP (fun n => (f n : ℤ)) 4 := by sorry

end Erdos195
