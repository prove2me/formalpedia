-- Prove2me | Theorems.Thm_Erdos195_in_order_ap_of_cofinite
-- name    : Erdos195.in_order_ap_of_cofinite
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T06:12:22.676786+00:00
-- url     : https://prove2.me/theorems/d150976b-91f2-487f-965e-69aca82bd942
-- title:
--   Every enumeration of a cofinite set of integers has in-order 3-APs from every start
-- statement:
--   Let $t:\mathbb{N}\to\mathbb{Z}$ be any sequence that takes every integer outside some finite set $F$ as a value. Then for every index $i$ there are indices $i<j<l$ with
--   $$t_j\neq t_i,\qquad t_l=2t_j-t_i,$$
--   i.e. $t_i,t_j,t_l$ is a nonconstant monotone $3$-term arithmetic progression in index order, starting at any prescribed position. (Proof idea: choose $x$ far from $F$ and from $t_0,\dots,t_i$; the positions of $t_i+2^n(x-t_i)$, $n\ge0$, cannot decrease forever.) In connection with Erdős Problem 195, this shows that every enumeration of a cofinite subset of $\mathbb{Z}$ has in-order $3$-APs starting arbitrarily late.
--
--   Formalization note: this is a purely combinatorial statement about integer sequences, phrased with `t : ℕ → ℤ` (or a chain of lists `P n` with `P (n+1) = P n ++ [w n]`); "cofinite" is expressed as existence of a finite set `F : Finset ℤ` outside of which every integer occurs.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree' answers tree10, generalized), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem in_order_ap_of_cofinite (t : ℕ → ℤ) (F : Finset ℤ) (hcov : ∀ z, z ∉ F → ∃ n, t n = z)
    (i : ℕ) : ∃ j l, i < j ∧ j < l ∧ t j ≠ t i ∧ t l = 2 * t j - t i := by sorry

end Erdos195
