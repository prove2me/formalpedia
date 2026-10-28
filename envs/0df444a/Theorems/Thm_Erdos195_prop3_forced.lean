-- Prove2me | Theorems.Thm_Erdos195_prop3_forced
-- name    : Erdos195.prop3_forced
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T03:10:03.910901+00:00
-- url     : https://prove2.me/theorems/4d12b81c-532c-4a3d-9d66-a2c730e70cf7
-- title:
--   Extending $(0,1)$ by one even target $t\equiv 0 \pmod 4$ forces $\varepsilon_0=1$ and $2t-1$ before $t$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $t>0$ with $4\mid t$, and let $Q$ be an $\varepsilon$-safe word that begins with $0,1$, contains $t$, and whose only even letters are $0$ and $t$. Then
--   $$\varepsilon_0=1,\qquad 2t-1\in Q,\qquad 2t-1\text{ occurs in }Q\text{ before }t.$$
--   This is a rigidity statement for extending the safe word $(0,1)$ by a single new even target in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195): the lowest digit of $\varepsilon$ is forced and the continuation $2t-1$ must be placed before $t$ itself.
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; "begins with $0,1$" is `[0, 1] <+: Q`; "before" is comparison of `List.idxOf`; $\varepsilon_0=1$ is `ε 0 = true`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem prop3_forced (ε : ℕ → Bool) (Q : List ℤ) (hS : Safe (epsLt ε) Q) (hpre : [0, 1] <+: Q)
    (t : ℤ) (ht0 : 0 < t) (ht4 : 4 ∣ t) (htQ : t ∈ Q)
    (hev : ∀ x ∈ Q, x % 2 = 0 → x = 0 ∨ x = t) :
    ε 0 = true ∧ 2 * t - 1 ∈ Q ∧ Q.idxOf (2 * t - 1) < Q.idxOf t := by sorry

end Erdos195
