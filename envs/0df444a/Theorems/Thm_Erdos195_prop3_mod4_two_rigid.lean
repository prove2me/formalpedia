-- Prove2me | Theorems.Thm_Erdos195_prop3_mod4_two_rigid
-- name    : Erdos195.prop3_mod4_two_rigid
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T03:43:08.192791+00:00
-- url     : https://prove2.me/theorems/f31b568f-bb1b-4cb9-9002-529c5b337950
-- title:
--   Extending $(0,1)$ by one even target $t\equiv2\pmod4$ with $\varepsilon_0=0$ forces $t=2\cdot3^n$ and odd letters $=\{3^i\}$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $t>0$ with $t\equiv 2\pmod 4$, and let $Q$ be an $\varepsilon$-safe word that begins with $0,1$, contains $t$, and whose only even letters are $0$ and $t$. If $\varepsilon_0=0$, then there is $n\ge0$ with
--   $$t=2\cdot 3^n\qquad\text{and}\qquad \{y\in Q : y \text{ odd}\}=\{1,3,9,\dots,3^n\}.$$
--   Thus, outside the very thin family $t=2\cdot3^n$, extending the safe word $(0,1)$ by one even target $t\equiv2\pmod4$ forces $\varepsilon_0=1$, and even in that family the odd letters are completely determined. This complements the case $t\equiv0\pmod4$, where $\varepsilon_0=1$ is always forced (Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$, Erdős Problem 195).
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; "begins with $0,1$" is `[0, 1] <+: Q`; $\varepsilon_0=0$ is `ε 0 = false`; the set equality is stated as membership of all $3^i$ ($i\le n$) plus every odd letter being some $3^i$ with $i\le n$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem prop3_mod4_two_rigid (ε : ℕ → Bool) (Q : List ℤ) (hS : Safe (epsLt ε) Q)
    (hpre : [0, 1] <+: Q) (t : ℤ) (ht0 : 0 < t) (ht2 : t % 4 = 2) (htQ : t ∈ Q)
    (hev : ∀ x ∈ Q, x % 2 = 0 → x = 0 ∨ x = t) (hε : ε 0 = false) :
    ∃ n : ℕ, t = 2 * 3 ^ n ∧ (∀ i ≤ n, (3:ℤ) ^ i ∈ Q) ∧
      ∀ y ∈ Q, y % 2 = 1 → ∃ i ≤ n, y = 3 ^ i := by sorry

end Erdos195
