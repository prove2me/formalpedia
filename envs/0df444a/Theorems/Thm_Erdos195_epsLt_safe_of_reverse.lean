-- Prove2me | Theorems.Thm_Erdos195_epsLt_safe_of_reverse
-- name    : Erdos195.epsLt_safe_of_reverse
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:51:13.428402+00:00
-- url     : https://prove2.me/theorems/95bb0d70-e5b7-405b-a5fb-c52fb3ac306a
-- title:
--   Reverse-order safety for $\varepsilon$-orders
-- statement:
--   Let $P=(p_1,\dots,p_n)$ be a finite list of integers listed in strictly decreasing $\prec_\varepsilon$-order ($p_j\prec_\varepsilon p_i$ whenever $i<j$). Then $P$ is safe for $\prec_\varepsilon$: the completion order (first $P$ in list order, then the remaining integers in $\prec_\varepsilon$-order) contains no monotone $4$-term progression.
--
--   $$P \text{ listed in reverse } \prec_\varepsilon\text{-order} \implies \mathrm{Safe}_{\prec_\varepsilon}(P).$$
--
--   This is the $\mathbb{Z}$-version of Ho's Lemma 1, the base case of the extension procedure.
--
--   **Formalization Note** `compLt R P x y` holds when both lie in `P` with `x` at a smaller index, or `x ∈ P` and `y ∉ P`, or neither lies in `P` and `R x y`. `Safe R P` says there are no `a` and `r ≠ 0` with `compLt R P a (a+r)`, `compLt R P (a+r) (a+2r)` and `compLt R P (a+2r) (a+3r)`. `epsLt ε x y` is `x ≠ y ∧ (x / 2^k % 2 = 1 ↔ ε k = true)` with `k = padicValInt 2 (y - x)`, i.e. $k=\nu_2(y-x)$; integer division is floor division, so `x / 2^k % 2` is the $k$-th two's-complement digit of $x$.
-- source:
--   B. S. Ho, arXiv:2609.12780, Lemma 1 ('Every finite set, listed in reverse ◁-order, is a safe word'); here over ℤ for all ε

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_safe_of_reverse (ε : ℕ → Bool) (P : List ℤ)
    (hP : P.Pairwise (fun x y => epsLt ε y x)) : Safe (epsLt ε) P := by sorry

end Erdos195
