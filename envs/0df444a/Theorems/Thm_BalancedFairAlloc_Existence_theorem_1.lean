-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_theorem_1
-- name    : BalancedFairAlloc.Existence.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:56.369826+00:00
-- url     : https://prove2.me/theorems/be2b1823-f764-4817-b715-c26a327dbf84
-- title:
--   Theorem 1 — every additive mixed-manna instance has a balanced allocation that is EF[1,1] and fPO in P_bal, and swapEF when n divides m
-- statement:
--   Let $n\ge1$ agents share $m$ indivisible items, agent $i$ valuing item $g$ at $v_{ig}\in\mathbb R$ (any sign) and bundles additively. Then there is one complete integral allocation $A$ such that
--
--   $$A\ \text{balanced}\ \ \wedge\ \ A\ \text{EF[1,1]}\ \ \wedge\ \ A\ \text{fPO in }P_{\mathrm{bal}}\ \ \wedge\ \ \big(n\mid m\Rightarrow A\ \text{swapEF}\big).$$
--
--   Here balanced means $|A_i|\in\{\lfloor m/n\rfloor,\lfloor m/n\rfloor+1\}$; EF[1,1] means that for all $i,j$ some $C\subseteq A_i$, $G\subseteq A_j$ with $|C|,|G|\le1$ give $v_i(A_i\setminus C)\ge v_i(A_j\setminus G)$; fPO in $P_{\mathrm{bal}}$ means that no balanced fractional allocation $x\in P_{\mathrm{bal}}$ has $v_i(x_i)\ge v_i(A_i)$ for all $i$ with one strict inequality; swapEF means that for all $i,j$ either $v_i(A_i)\ge v_i(A_j)$ or some $h\in A_i$, $g\in A_j$ give $v_i((A_i\setminus\{h\})\cup\{g\})\ge v_i((A_j\setminus\{g\})\cup\{h\})$.
--
--   This is the paper's main result; it settles the existence of balanced EF1 and fPO allocations for goods and for chores, and of balanced swapEF and PO allocations for additive valuations.
--
--   Differences from the source:
--   - reading: fPO → fPO in P_bal: no balanced fractional allocation Pareto dominates A (`IsFPOIn v (Pbal n m) (allocMatrix A)`); reason: footnote 1 (p. 1): for balanced allocations PO and fPO are interpreted with respect to balanced integral and fractional allocations; fPO against all fractional allocations is false (footnote 1's example)
--   - encoding: a balanced allocation (complete, |A_i| ∈ {⌊m/n⌋, ⌈m/n⌉}) → a map `Fin m → Fin n` with |A_i| ∈ {m / n, m / n + 1}; reason: balanced allocations are complete (P_bal requires ∑_i x_ig = 1); for complete allocations the two size conditions agree
--   - encoding: an instance with agents N = [n] → hypothesis 1 ≤ n, agents `Fin n` numbered from 0; reason: m = nr + s with s < n presupposes n ≥ 1; with n = 0 and m > 0 there is no allocation
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 2 (PDF 4), Theorem 1; restated p. 11 (PDF 13)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model

namespace BalancedFairAlloc.Existence

theorem theorem_1 (n m : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) :
    ∃ A : Allocation n m,
      IsBalanced A ∧ IsEF11 v A ∧ IsFPOIn v (Pbal n m) (allocMatrix A) ∧
      (n ∣ m → IsSwapEF v A) := by sorry

end BalancedFairAlloc.Existence
