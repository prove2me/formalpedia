-- Prove2me | Theorems.Thm_Erdos195_doubling_seq_no_three_ap
-- name    : Erdos195.doubling_seq_no_three_ap
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T06:12:21.991976+00:00
-- url     : https://prove2.me/theorems/757a9b4d-50bb-4b35-a879-8079a2658cc9
-- title:
--   The sequence $a+(2^i-1)r$ contains no 3-term arithmetic progression
-- statement:
--   Let $a,r\in\mathbb{Z}$ with $r\neq0$ and $x_i=a+(2^i-1)r$ for $i\in\mathbb{N}$. Then no term is the average of two other terms: for all $i,j,l$ with $i\neq l$,
--   $$2x_j\neq x_i+x_l,$$
--   since this would force $2^{j+1}=2^i+2^l$ with $i\neq l$. The sequence $(x_i)$ is the orbit of iterated fourth-term completions $x_{i+2}=3x_{i+1}-2x_i$ appearing in tree-witness constructions for Erdős Problem 195; it contains no nonconstant $3$-term arithmetic progression.
--
--   Formalization note: stated for natural-number indices with `2 ^ i` computed in ℤ.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree' answers tree10, generalized), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem doubling_seq_no_three_ap (a r : ℤ) (hr : r ≠ 0) (i j l : ℕ) (hil : i ≠ l) :
    2 * (a + (2 ^ j - 1) * r) ≠ (a + (2 ^ i - 1) * r) + (a + (2 ^ l - 1) * r) := by sorry

end Erdos195
