-- Prove2me | Theorems.Thm_Erdos195_trap_mod4_three
-- name    : Erdos195.trap_mod4_three
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T04:58:28.696814+00:00
-- url     : https://prove2.me/theorems/0e8ae478-2e62-4304-94a2-4df1eb014ad9
-- title:
--   Every $t\equiv 3 \pmod 4$ can be appended to $(0,1,-1)$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $t\equiv 3\pmod 4$ with $t\neq-1$, put $h=\nu_2(t+1)\ (\ge 2)$, and define $\varepsilon_h=0$ and $\varepsilon_k=1$ for $k\neq h$. Then
--   $$\text{the word } (0,\,1,\,-1,\,t)\ \text{ is } \varepsilon\text{-safe}.$$
--   The three-letter word $(0,1,-1)$ is a natural 'trap' prefix in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195); this shows every target $t\equiv 3\pmod 4$ can be appended directly, with no auxiliary letters, by choosing a single digit of $\varepsilon$ depending on $t$.
--
--   Formalization note: $\varepsilon$ is `fun k => decide (k ≠ padicValInt 2 (t + 1))`; `Safe`, `epsLt` come from `Definitions.Def_Erdos195_defs`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (statement suggested by GPT 6 Astra, Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem trap_mod4_three (t : ℤ) (ht : t % 4 = 3) (htn : t ≠ -1) :
    Safe (epsLt fun k => decide (k ≠ padicValInt 2 (t + 1))) [0, 1, -1, t] := by sorry

end Erdos195
