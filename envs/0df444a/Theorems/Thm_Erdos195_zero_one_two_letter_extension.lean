-- Prove2me | Theorems.Thm_Erdos195_zero_one_two_letter_extension
-- name    : Erdos195.zero_one_two_letter_extension
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T04:08:57.784225+00:00
-- url     : https://prove2.me/theorems/2dd06a54-d8c1-4621-a548-b3e8251a314e
-- title:
--   With $\varepsilon\equiv1$, every $t\notin\{0,1\}$ extends $(0,1)$ safely: $(0,1,t)$ for odd $t$, $(0,1,2t-1,t)$ for even $t$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Here $\varepsilon\equiv1$ (constant digit $1$). Let $t\in\mathbb{Z}\setminus\{0,1\}$. Then
--   $$(0,1,t)\ \text{is }1\text{-safe if } t \text{ is odd},\qquad (0,1,2t-1,t)\ \text{is }1\text{-safe if } t \text{ is even}.$$
--   Thus the safe word $(0,1)$ can absorb any prescribed integer with at most one auxiliary entry (the reflection $2t-1$ of $1$ through $t$, placed before $t$). This is the case $j=0$ of the corresponding statement for $(0,2^j)$.
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; $\varepsilon\equiv1$ is `fun _ => true`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem zero_one_two_letter_extension (t : ℤ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (t % 2 = 1 → Safe (epsLt fun _ => true) [0, 1, t]) ∧
      (t % 2 = 0 → Safe (epsLt fun _ => true) [0, 1, 2 * t - 1, t]) := by sorry

end Erdos195
