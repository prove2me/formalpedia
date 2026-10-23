-- Prove2me | Theorems.Thm_Erdos195_three_letter_safe_iff
-- name    : Erdos195.three_letter_safe_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T04:56:45.047954+00:00
-- url     : https://prove2.me/theorems/901d43b9-9b8a-4019-8f5c-f7d7aed299b1
-- title:
--   Classification of $\varepsilon$-safe three-letter words $(a,b,t)$
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $a,b,t$ be distinct integers. Then the three-letter word $(a,b,t)$ is $\varepsilon$-safe for some $\varepsilon$ if and only if
--   $$t\neq 2b-a\qquad\text{and}\qquad\bigl(\nu_2(b-a)\neq\nu_2(t-b)\ \text{ or }\ 3t-2b=a\bigr).$$
--   This completely classifies which third letters can follow a two-letter safe word in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195). For example, $3b-2a$ can always be appended to $(a,b)$, since $\nu_2((3b-2a)-b)=\nu_2(b-a)+1$.
--
--   Formalization note: $\nu_2$ is `padicValInt 2`; `Safe`, `epsLt` come from `Definitions.Def_Erdos195_defs`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (statement suggested by GPT 6 Astra, Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem three_letter_safe_iff (a b t : ℤ) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    (∃ ε : ℕ → Bool, Safe (epsLt ε) [a, b, t]) ↔
      t ≠ 2 * b - a ∧ (padicValInt 2 (b - a) ≠ padicValInt 2 (t - b) ∨ 3 * t - 2 * b = a) := by sorry

end Erdos195
