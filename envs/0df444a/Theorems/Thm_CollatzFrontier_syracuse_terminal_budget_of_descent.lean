-- Prove2me | Theorems.Thm_CollatzFrontier_syracuse_terminal_budget_of_descent
-- name    : CollatzFrontier.syracuse_terminal_budget_of_descent
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:25:18.409985+00:00
-- url     : https://prove2.me/theorems/2513a4d3-77eb-4b93-9876-33755812122c
-- title:
--   Residue-class Syracuse descent from a truncated terminal divisor
-- statement:
--   Let $T$ be the Syracuse map, $T(n)=(3n+1)/2^{v_2(3n+1)}$. Suppose a finite sequence of exact affine steps $b_0=r,b_1,\dots,b_k$ with exponents $a_0,\dots,a_{k-1}$ satisfies
--
--   $$3\,b_i+1=2^{a_i}\,b_{i+1}\qquad(i<k),\qquad b_{i+1}\text{ odd},$$
--
--   and a terminal row closes the chain with a not necessarily exact divisor exponent $e$,
--
--   $$3\,b_k+1=2^{e}B,\qquad B<r=b_0.$$
--
--   If the total exponent budget fits the modulus, $\big(\sum_{i<k}a_i\big)+e\le K$, then $T^{k+1}(r+2^K q) < r+2^K q$ for every natural number $q$.
--
--   **Why the terminal exponent need not be exact.** It is only required that $2^e$ *divides* $3b_k+1$, with quotient $B$, not that $e$ be the true 2-adic valuation $v_2(3b_k+1)$; the exact-prefix transfer still pins the orbit down through step $k$, and the terminal row only needs to bound the last image from above by $B$ plus a budget-respecting multiple of $2^K$, which $B<r$ already makes strict.
--
--   **Application.** For the representative $1863$, fourteen Syracuse steps use thirteen *exact* rows (total exponent $20$) followed by one *truncated* terminal row with $e=3$ (a genuine divisor of the true final numerator, not its full valuation), reaching budget $K=23$ — three bits tighter than using the chain's full valuation sum of $26$. This gives $T^{14}(1863+2^{23}q)<1863+2^{23}q$ for every natural $q$.
--
--   **Formalization note.** The hypotheses `hstep`/`hodd` pin down the exact intermediate orbit as in the fully-exact interface; only the single terminal divisibility `hfinal` is allowed to be inexact, together with the ordinary descent comparison `hdesc : B < r`.
-- source:
--   collatz-frontier (private repo), commit 4d656b9c9c5815305bd391f206c9d3e9587dd395, lean/CollatzFrontier/AffineDrift.lean, declaration syracuse_terminal_budget_of_descent (building on lean/CollatzFrontier/TerminalBudget.lean, declaration syracuse_terminal_budget, and lean/CollatzFrontier/AffineStep.lean), with the unused hypothesis `he : 0 < e` dropped (grep of the repo proof body shows `he` is only threaded through, never used). The 1863 application is lean/CollatzFrontier/TerminalBudget.lean, declaration syracuse_descent_1863_from_budget. Original result of this contribution; no claim of prior-literature novelty beyond the classical affine-orbit observation is made.

import Definitions.Def_syracuseStep
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

namespace CollatzFrontier

theorem syracuse_terminal_budget_of_descent
    (a b : ℕ → ℕ) (r K k e B : ℕ)
    (hstart : b 0 = r)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < k, Odd (b (i + 1)))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hbudget : (∑ i ∈ Finset.range k, a i) + e ≤ K)
    (hdesc : B < r) (q : ℕ) :
    syracuseStep^[k + 1] (r + 2 ^ K * q) < r + 2 ^ K * q := by sorry

end CollatzFrontier
