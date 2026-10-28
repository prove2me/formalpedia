-- Prove2me | Theorems.Thm_Erdos624_robust_alon_count
-- name    : Erdos624.robust_alon_count
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:27:39.216883+00:00
-- url     : https://prove2.me/theorems/346ea7ac-6abe-4c75-bd22-72525acd76ca
-- title:
--   Robust Alon bound for Erdős 624: at least $1/64$ of all $k$-sets miss $n/64$ points
-- statement:
--   Let $X$ be a set with $n=2^k$ elements, $k\ge3$, and let $f:\mathcal P(X)\to X$ be arbitrary. For a $k$-subset $Y\subseteq X$ write $L_f(Y)=n-|\{f(A):A\subseteq Y\}|$ for the number of points of $X$ missed by $f$ on the subsets of $Y$. Let $\mathcal K=\binom{X}{k}$. **Theorem.**
--
--   $$|\mathcal K|\;\le\;64\,\bigl|\{Y\in\mathcal K:\ n\le 64\,L_f(Y)\}\bigr|,$$
--
--   i.e. $\Pr_Y\bigl(L_f(Y)\ge n/64\bigr)\ge 1/64$ for a uniformly random $k$-set $Y$.
--
--   It follows from the averaged bound `robust_alon_sum` since $0\le L_f\le n$. This is the 'robust Alon' statement: a linear number of points is missed with constant probability, uniformly in $f$.
--
--   **Formalization Note.** $X=\mathrm{Fin}\,(2^k)$; the statement is in counting form (sums over $k$-subsets, natural numbers), with no probability.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; (B.5) of claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem robust_alon_count (k : ℕ) (hk : 3 ≤ k) (f : Finset (Fin (2 ^ k)) → Fin (2 ^ k)) :
    #(powersetCard k (univ : Finset (Fin (2 ^ k)))) ≤
      64 * #((powersetCard k (univ : Finset (Fin (2 ^ k)))).filter
        (fun Y => 2 ^ k ≤ 64 * (2 ^ k - #(Y.powerset.image f)))) := by sorry

end Erdos624
