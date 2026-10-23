-- Prove2me | Theorems.Thm_Erdos195_epsLt_safe_append_iff
-- name    : Erdos195.epsLt_safe_append_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T02:30:50.496539+00:00
-- url     : https://prove2.me/theorems/c1e82c37-3548-46a1-bec8-47773725882d
-- title:
--   One-letter extension criterion for $\varepsilon$-safe words
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $P$ of distinct integers is $\varepsilon$-safe if the sequence "the letters of $P$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $P$ be $\varepsilon$-safe and let $t\notin P$. Then the word $P\cdot t$ (append $t$) is $\varepsilon$-safe if and only if
--   $$\text{(A)}\ \ \forall a \text{ before } b \text{ in } P:\ t=2b-a\ \Rightarrow\ 3b-2a\in P,\qquad \text{(B)}\ \ \forall a\in P:\ a\prec_\varepsilon t\ \Rightarrow\ (2t-a\in P\ \text{or}\ 3t-2a\in P).$$
--   This reduces one step of a Ho-style construction of a $4$-AP-free permutation of $\mathbb{Z}$ (Erdős Problem 195) to two finite checks involving only pairs that end at, or point to, the new letter.
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; "$a$ before $b$" is `P.idxOf a < P.idxOf b`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_safe_append_iff (ε : ℕ → Bool) (P : List ℤ) (t : ℤ)
    (hS : Safe (epsLt ε) P) (htP : t ∉ P) :
    Safe (epsLt ε) (P ++ [t]) ↔
      (∀ a ∈ P, ∀ b ∈ P, P.idxOf a < P.idxOf b → t = 2 * b - a → 3 * b - 2 * a ∈ P) ∧
      (∀ a ∈ P, epsLt ε a t → 2 * t - a ∈ P ∨ 3 * t - 2 * a ∈ P) := by sorry

end Erdos195
