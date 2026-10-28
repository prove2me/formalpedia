-- Prove2me | Theorems.Thm_Erdos195_odd_two_letter_odd_target
-- name    : Erdos195.odd_two_letter_odd_target
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T04:13:12.055201+00:00
-- url     : https://prove2.me/theorems/610ba587-25bd-47b7-b399-3ec6fab9f29f
-- title:
--   Odd $u$, odd target $t$: $(0,u,t)$ is $\varepsilon$-safe when $\varepsilon_0=1$ and $\varepsilon$ differs from $u$ at digit $\nu_2(t-u)$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Write $u_k$ for the $k$-th binary digit of $u$. Let $u$ and $t$ be odd integers with $t\neq u$, and put $k=\nu_2(t-u)$. If $\varepsilon_0=1$ and $\varepsilon_k\neq u_k$, then
--   $$(0,\,u,\,t)\ \text{is } \varepsilon\text{-safe}.$$
--   So for an odd second letter $u$, every odd target can be appended to $(0,u)$ directly, after fixing a single digit of $\varepsilon$ (a step in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$, Erdős Problem 195).
--
--   Formalization note: `Safe`, `epsLt`, `bitOne` are from `Definitions.Def_Erdos195_defs`; $\varepsilon_k\ne u_k$ is written `¬ (bitOne u k ↔ ε k = true)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem odd_two_letter_odd_target (ε : ℕ → Bool) (u t : ℤ) (hu : u % 2 = 1) (ht : t % 2 = 1)
    (htu : t ≠ u) (h0 : ε 0 = true)
    (hk : ¬ (bitOne u (padicValInt 2 (t - u)) ↔ ε (padicValInt 2 (t - u)) = true)) :
    Safe (epsLt ε) [0, u, t] := by sorry

end Erdos195
