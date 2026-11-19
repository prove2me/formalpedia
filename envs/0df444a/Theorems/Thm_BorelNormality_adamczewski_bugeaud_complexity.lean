-- Prove2me | Theorems.Thm_BorelNormality_adamczewski_bugeaud_complexity
-- name    : BorelNormality.adamczewski_bugeaud_complexity
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T17:10:19.127785+00:00
-- url     : https://prove2.me/theorems/bc314137-1b88-4fd7-ae2a-da19bb5105dd
-- title:
--   Adamczewski–Bugeaud Theorem 1: complexity of algebraic expansions
-- statement:
--   Adamczewski–Bugeaud (2007), Theorem 1. Let $b \ge 2$ be an integer and let $x$ be an irrational algebraic real number. The complexity function $p(n)$ of the base-$b$ expansion of $x$ — the number of distinct blocks of $n$ digits occurring in it — satisfies
--
--   $$\liminf_{n \to \infty} \frac{p(n)}{n} = +\infty.$$
--
--   This is the strongest known general result about the digit expansions of irrational algebraic numbers, and the closest approach to Borel's conjecture to date: a number normal in base $b$ has $p(n) = b^n$, so the theorem is a very weak shadow of the conjectured behaviour. Its proof is a combinatorial transcendence criterion derived from the Schmidt Subspace Theorem. In particular every irrational real number with sub-linear complexity ($p(n) = O(n)$) is transcendental.
--
--   **Formalization Note.** The limit inferior is taken in `ENNReal` ($\mathbb{R}_{\ge 0}\cup\{\infty\}$) along `Filter.atTop`, with value `⊤` ($+\infty$); this is equivalent to $p(n)/n \to +\infty$. The complexity function is `BorelNormality.complexity` from the mission's definition file.
-- source:
--   B. Adamczewski, Y. Bugeaud, On the complexity of algebraic numbers I. Expansions in integer bases, Ann. of Math. (2) 165 (2007), no. 2, 547–565, Theorem 1 (Section 2), https://doi.org/10.4007/annals.2007.165.547. Verbatim: 'Let b ≥ 2 be an integer. The complexity function of the b-ary expansion of every irrational algebraic number satisfies liminf_{n→∞} p(n)/n = +∞.'

import Mathlib
import Definitions.Def_Normal_Core
import Definitions.Def_BorelNormality_Complexity

set_option autoImplicit false

namespace BorelNormality

theorem adamczewski_bugeaud_complexity (x : ℝ) (hx : IsAlgebraic ℚ x) (hi : Irrational x)
    (b : ℕ) (hb : 2 ≤ b) :
    Filter.liminf (fun n : ℕ => (complexity b x n : ENNReal) / (n : ENNReal)) Filter.atTop = ⊤ := by sorry

end BorelNormality
