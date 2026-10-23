-- Prove2me | Theorems.Thm_Erdos195_zero_u_two_helper_fail
-- name    : Erdos195.zero_u_two_helper_fail
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T04:52:02.365385+00:00
-- url     : https://prove2.me/theorems/9b6d2b9d-67ba-4e49-8f16-0bf9d7d6f19f
-- title:
--   Three two-helper extensions of $(0,u)$, $u\equiv 3$, by $t\equiv 2 \pmod 4$ are never safe
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $u\equiv 3\pmod 4$, $t\equiv 2\pmod 4$, and put $s=2t-u$, $d=3t-2u$, $h=6t-5u$. Let $Q$ be an $\varepsilon$-safe word (any $\varepsilon$) that begins with $0,u$. Then, regardless of the order of the remaining letters:
--   $$\text{(i) if } s,3t\in Q,\ \text{then } Q\not\subseteq\{0,u,s,3t,t\};\quad \text{(ii) if } t,h\in Q,\ \text{then } Q\not\subseteq\{0,u,s,h,t\};\quad \text{(iii) if } 3t\neq 2u \text{ and } d\in Q,\ \text{then } Q\not\subseteq\{0,u,d,s,t\}.$$
--   These are the three natural two-helper candidates for absorbing a target $t\equiv2\pmod4$ into the safe word $(0,u)$ with $u\equiv 3\pmod 4$ in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195); each fails because two open in-order pairs force contradictory values of the same digit $\varepsilon_0$ or $\varepsilon_1$.
--
--   Formalization note: "begins with $0,u$" is `[0, u] <+: Q`; set inclusions are stated letterwise as disjunctions of equalities; `Safe`, `epsLt` come from `Definitions.Def_Erdos195_defs`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (statement suggested by GPT 6 Astra, Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem zero_u_two_helper_fail (ε : ℕ → Bool) (u t : ℤ) (hu : u % 4 = 3) (ht : t % 4 = 2)
    (Q : List ℤ) (hpre : [0, u] <+: Q) (hS : Safe (epsLt ε) Q) :
    (2 * t - u ∈ Q → 3 * t ∈ Q →
      ¬ ∀ x ∈ Q, x = 0 ∨ x = u ∨ x = 2 * t - u ∨ x = 3 * t ∨ x = t) ∧
    (t ∈ Q → 6 * t - 5 * u ∈ Q →
      ¬ ∀ x ∈ Q, x = 0 ∨ x = u ∨ x = 2 * t - u ∨ x = 6 * t - 5 * u ∨ x = t) ∧
    (3 * t ≠ 2 * u → 3 * t - 2 * u ∈ Q →
      ¬ ∀ x ∈ Q, x = 0 ∨ x = u ∨ x = 3 * t - 2 * u ∨ x = 2 * t - u ∨ x = t) := by sorry

end Erdos195
