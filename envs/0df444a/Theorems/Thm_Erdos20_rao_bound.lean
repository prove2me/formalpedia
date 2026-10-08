-- Prove2me | Theorems.Thm_Erdos20_rao_bound
-- name    : Erdos20.rao_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:30:29.619145+00:00
-- url     : https://prove2.me/theorems/debf533f-3f74-4d21-827c-0de164d4548b
-- title:
--   Rao's bound $f(n,k) \le (\alpha k\log(kn))^n + 1$
-- statement:
--   Let $f(n,k)$ be the sunflower threshold. There is a universal constant $\alpha > 1$ such that for all integers $n \ge 1$ and $k \ge 2$,
--
--   $$f(n,k) \le \bigl(\alpha\, k \log(kn)\bigr)^n + 1,$$
--
--   i.e. every family of more than $(\alpha k\log(kn))^n$ sets of size $n$ contains a $k$-sunflower (Rao 2020, Theorem 1, with $p = k$ petals and set size $n$).
--
--   **Formalization Note** $\log$ is the natural logarithm (Rao uses base $2$; the change of base only rescales $\alpha$ and preserves $\alpha > 1$). "More than $X$ sets forces a sunflower" is encoded as $f(n,k) \le X + 1$ in $\mathbb R$.
-- source:
--   A. Rao, Coding for sunflowers, Discrete Analysis 2020:2, doi:10.19086/da.11887, arXiv:1909.04774, Theorem 1

import Definitions.Def_Erdos20_defs
import Mathlib

namespace Erdos20
theorem rao_bound :
    ∃ C : ℝ, 1 < C ∧ ∀ n k : ℕ, 0 < n → 2 ≤ k →
      (f n k : ℝ) ≤ (C * k * Real.log ((k : ℝ) * n)) ^ n + 1 := by sorry
end Erdos20
