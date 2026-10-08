-- Prove2me | Theorems.Thm_CompOT_Duality_proposition_3_1
-- name    : CompOT.Duality.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:43.070557+00:00
-- url     : https://prove2.me/theorems/40593259-bbcc-420e-824d-eec0816f13d9
-- title:
--   Proposition 3.1, pp. 403–404 — f ≤ f′ ⇒ f^C ≥ f′^C; f^{CC̄} ≥ f, g^{C̄C} ≥ g; f^{CC̄C} = f^C
-- statement:
--   Let $n, m \ge 1$ and $C \in \mathbb R^{n\times m}$. For $f \in \mathbb R^n$ and $g \in \mathbb R^m$ write $(f^C)_j = \min_i C_{i,j} - f_i$ and $(g^{\bar C})_i = \min_j C_{i,j} - g_j$. With inequalities between vectors read elementwise:
--
--   1. $f \le f' \;\Rightarrow\; f^C \ge f'^C$ for all $f, f' \in \mathbb R^n$;
--   2. $f^{C\bar C} \ge f$ for all $f \in \mathbb R^n$, and $g^{\bar C C} \ge g$ for all $g \in \mathbb R^m$;
--   3. $f^{C\bar C C} = f^C$ for all $f \in \mathbb R^n$.
--
--   Here $f^{C\bar C} = (f^C)^{\bar C}$ and so on. The proposition explains why alternating $C$- and $\bar C$-transforms to improve the dual objective stalls after one round.
--
--   **Formalization Note** The hypotheses $n \ge 1$ and $m \ge 1$ make both minima well defined (the book's index sets are nonempty).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.1, pp. 403–404

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- Proposition 3.1, pp. 403–404 (elementwise order on vectors):
(i) `f ≤ f′ ⇒ f^C ≥ f′^C`; (ii) `f^{C C̄} ≥ f` and `g^{C̄ C} ≥ g`; (iii) `f^{C C̄ C} = f^C`.
Both index sets are nonempty (`n, m ≥ 1`), so that the transforms are genuine minima. -/
theorem proposition_3_1 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (C : Matrix (Fin n) (Fin m) ℝ) :
    (∀ f f' : Fin n → ℝ, f ≤ f' → cTransform C f' ≤ cTransform C f) ∧
      (∀ f : Fin n → ℝ, f ≤ cbarTransform C (cTransform C f)) ∧
      (∀ g : Fin m → ℝ, g ≤ cTransform C (cbarTransform C g)) ∧
      (∀ f : Fin n → ℝ, cTransform C (cbarTransform C (cTransform C f)) = cTransform C f) := by sorry

end CompOT.Duality
