-- Prove2me | Theorems.Thm_Erdos195_two_pow_two_letter_extension
-- name    : Erdos195.two_pow_two_letter_extension
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T04:08:57.930984+00:00
-- url     : https://prove2.me/theorems/f620321f-5f42-4637-bf1b-3cf3065d5afd
-- title:
--   With $\varepsilon\equiv1$, every $t\notin\{0,2^j\}$ extends $(0,2^j)$ safely using at most one auxiliary letter $2t-2^j$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Here $\varepsilon\equiv1$ (constant digit $1$). Let $j\ge0$, $d=2^j$, and $t\in\mathbb{Z}\setminus\{0,d\}$. Then
--   $$(0,\,d,\,t)\ \text{is }1\text{-safe if } 2^{j+1}\nmid t,\qquad (0,\,d,\,2t-d,\,t)\ \text{is }1\text{-safe if } 2^{j+1}\mid t.$$
--   So every integer target can be absorbed into the two-letter word $(0,2^j)$ with at most one auxiliary letter, without changing $\varepsilon$: an explicit instance of the one-step extension problem underlying Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195).
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; $\varepsilon\equiv1$ is `fun _ => true`; words are Lean lists.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem two_pow_two_letter_extension (j : ℕ) (t : ℤ) (ht0 : t ≠ 0) (htd : t ≠ 2 ^ j) :
    (¬ (2:ℤ) ^ (j + 1) ∣ t → Safe (epsLt fun _ => true) [0, 2 ^ j, t]) ∧
      ((2:ℤ) ^ (j + 1) ∣ t → Safe (epsLt fun _ => true) [0, 2 ^ j, 2 * t - 2 ^ j, t]) := by sorry

end Erdos195
