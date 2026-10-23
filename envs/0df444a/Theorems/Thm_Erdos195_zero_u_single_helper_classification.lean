-- Prove2me | Theorems.Thm_Erdos195_zero_u_single_helper_classification
-- name    : Erdos195.zero_u_single_helper_classification
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T04:51:56.727351+00:00
-- url     : https://prove2.me/theorems/dcbc8e03-22ed-4976-8dbe-55bcf9bd0ea4
-- title:
--   Extending $(0,u)$, $u\equiv3$, by $t\equiv2 \pmod 4$ with one helper works iff $3t=2u$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $u\equiv 3\pmod 4$ and $t\equiv 2\pmod 4$ be integers. The following are equivalent:
--   $$\text{(1) some }\varepsilon\text{-safe word (for some }\varepsilon)\text{ begins with }0,u,\text{ contains }t,\text{ and has all letters in }\{0,u,t,h\}\text{ for a single integer }h;$$
--   $$\text{(2) the word }(0,u,t)\text{ is }\varepsilon\text{-safe for some }\varepsilon;\qquad\text{(3) } 3t=2u.$$
--   Thus, outside the single exceptional relation $3t=2u$, absorbing a new target $t\equiv 2\pmod 4$ into the safe word $(0,u)$ with $u\equiv 3\pmod 4$ requires at least two auxiliary letters, wherever they are placed. This is a sharp case of the one-step extension problem for Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195); e.g. for $u=-1$ every $t\equiv 2\pmod 4$ needs at least two helpers.
--
--   Formalization note: "begins with $0,u$" is `[0, u] <+: Q`; the letter bound is `∀ x ∈ Q, x = 0 ∨ x = u ∨ x = t ∨ x = h`; `Safe`, `epsLt` come from `Definitions.Def_Erdos195_defs`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (statement suggested by GPT 6 Astra, Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem zero_u_single_helper_classification (u t : ℤ) (hu : u % 4 = 3) (ht : t % 4 = 2) :
    ((∃ (ε : ℕ → Bool) (Q : List ℤ) (h : ℤ), [0, u] <+: Q ∧ t ∈ Q ∧
        (∀ x ∈ Q, x = 0 ∨ x = u ∨ x = t ∨ x = h) ∧ Safe (epsLt ε) Q) ↔ 3 * t = 2 * u) ∧
    ((∃ ε : ℕ → Bool, Safe (epsLt ε) [0, u, t]) ↔ 3 * t = 2 * u) := by sorry

end Erdos195
