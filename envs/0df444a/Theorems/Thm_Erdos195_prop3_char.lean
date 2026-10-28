-- Prove2me | Theorems.Thm_Erdos195_prop3_char
-- name    : Erdos195.prop3_char
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T03:37:13.581797+00:00
-- url     : https://prove2.me/theorems/2cdeca5a-0195-4579-a568-be9a92c8abf2
-- title:
--   Exact safety criterion for $(0,1)$ extended by one even target $t\equiv0\pmod 4$: reflection closure
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $t>0$ with $4\mid t$, and let $Q$ be a word that begins with $0,1$, contains $t$, and whose only even letters are $0$ and $t$. Let $Q_{\mathrm{odd}}$ be the word of odd letters of $Q$ (in order) rescaled by $y\mapsto (y-1)/2$, and $\varepsilon'_k=\varepsilon_{k+1}$. Then $Q$ is $\varepsilon$-safe if and only if
--   $$\varepsilon_0=1,\quad \varepsilon_{\nu_2(t)}=1,\quad Q_{\mathrm{odd}}\text{ is }\varepsilon'\text{-safe},\quad\text{and for every odd letter } y \text{ before } t:\ 2t-y\in Q \text{ and it occurs before } t.$$
--   So, for a single even target, safety reduces exactly to a one-digit-lower problem for the odd letters together with closure of the odd letters placed before $t$ under the reflection $y\mapsto 2t-y$. This sharpens the necessary conditions $\varepsilon_0=1$, $2t-1$ before $t$ (Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$, Erdős Problem 195).
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; "begins with $0,1$" is `[0, 1] <+: Q`; "before" is comparison of `List.idxOf`; $Q_{\mathrm{odd}}$ is `(Q.filter (· % 2 = 1)).map (fun x => (x - 1) / 2)`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem prop3_char (ε : ℕ → Bool) (Q : List ℤ) (hpre : [0, 1] <+: Q)
    (t : ℤ) (ht0 : 0 < t) (ht4 : 4 ∣ t) (htQ : t ∈ Q)
    (hev : ∀ x ∈ Q, x % 2 = 0 → x = 0 ∨ x = t) :
    Safe (epsLt ε) Q ↔
      ε 0 = true ∧ ε (padicValInt 2 t) = true ∧
      Safe (epsLt (fun k => ε (k + 1)))
        ((Q.filter (fun x => decide (x % 2 = 1))).map (fun x => (x - 1) / 2)) ∧
      ∀ y ∈ Q, y % 2 = 1 → Q.idxOf y < Q.idxOf t →
        2 * t - y ∈ Q ∧ Q.idxOf (2 * t - y) < Q.idxOf t := by sorry

end Erdos195
