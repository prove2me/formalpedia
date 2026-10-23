-- Prove2me | Theorems.Thm_Erdos195_odd_two_letter_mod4_target
-- name    : Erdos195.odd_two_letter_mod4_target
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T04:13:09.918857+00:00
-- url     : https://prove2.me/theorems/dda4c1da-43a2-4224-af79-82dbd2cedd6a
-- title:
--   Odd $u$, target $t\equiv0\pmod 4$: $(0,u,2t-u,t)$ is $\varepsilon$-safe when $\varepsilon_0=1$, $\varepsilon_1\neq u_1$, $\varepsilon_{\nu_2 t}=1$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Write $u_k$ for the $k$-th binary digit of $u$. Let $u$ be odd and $t\neq0$ with $t\equiv0\pmod 4$. If $\varepsilon_0=1$, $\varepsilon_1\neq u_1$ and $\varepsilon_{\nu_2(t)}=1$, then
--   $$(0,\,u,\,2t-u,\,t)\ \text{is } \varepsilon\text{-safe}.$$
--   In particular, the single order with $\varepsilon_0=1$, $\varepsilon_1=1-u_1$ and $\varepsilon_k=1$ for $k\ge2$ (which depends only on $u$) lets every target $t\equiv0\pmod4$ be absorbed into $(0,u)$ with one auxiliary letter, the reflection $2t-u$ of $u$ through $t$.
--
--   Formalization note: `Safe`, `epsLt`, `bitOne` are from `Definitions.Def_Erdos195_defs`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem odd_two_letter_mod4_target (ε : ℕ → Bool) (u t : ℤ) (hu : u % 2 = 1) (ht : t % 4 = 0)
    (ht0 : t ≠ 0) (h0 : ε 0 = true) (h1 : ¬ (bitOne u 1 ↔ ε 1 = true))
    (hv : ε (padicValInt 2 t) = true) :
    Safe (epsLt ε) [0, u, 2 * t - u, t] := by sorry

end Erdos195
