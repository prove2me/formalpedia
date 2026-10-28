-- Prove2me | Theorems.Thm_Erdos195_erdos_195_exists_fourAP_free
-- name    : Erdos195.erdos_195_exists_fourAP_free
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:30:42.707578+00:00
-- url     : https://prove2.me/theorems/0dfb0e19-1b29-4696-88fc-dbfe5b6543c0
-- title:
--   Erdős #195: a permutation of $\mathbb{Z}$ with no monotone $4$-term AP
-- statement:
--   There is an arrangement $a_0,a_1,a_2,\dots$ of all the integers, each appearing exactly once, with no monotone $4$-term arithmetic progression:
--
--   $$\exists f:\mathbb{N}\simeq\mathbb{Z}\ \text{ such that there are no } i_1<i_2<i_3<i_4 \text{ with } f(i_1),f(i_2),f(i_3),f(i_4) \text{ an increasing or decreasing AP.}$$
--
--   Since every permutation of $\mathbb{Z}$ contains a monotone $3$-term progression (Davis–Entringer–Graham–Simmons 1977), this statement says that the answer to Erdős Problem 195 is $3$. Its negation says that the answer is $4$ (Adenwalla 2024 gives the upper bound $4$).
--
--   **Formalization Note** Permutations are `f : ℕ ≃ ℤ`; `HasMonotoneAP` is copied verbatim from formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`): a list of indices `l` with `l.Pairwise (· < ·)` whose image is an arithmetic progression of length $k$, listed forwards or backwards.
-- source:
--   Erdős Problem 195, https://www.erdosproblems.com/195 ; google-deepmind/formal-conjectures FormalConjectures/ErdosProblems/195.lean (erdos_195). Open.

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem erdos_195_exists_fourAP_free : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 := by sorry

end Erdos195
