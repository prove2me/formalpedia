-- Prove2me | Theorems.Thm_CompOT_Duality_sec_3_2_ctransform_admissible
-- name    : CompOT.Duality.sec_3_2_ctransform_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:31.255685+00:00
-- url     : https://prove2.me/theorems/3ae16870-85d8-4ef5-a201-8037a9417d7f
-- title:
--   §3.2, p. 403 — (f, f^C) ∈ R(C), and f^C is the largest g with (f, g) ∈ R(C)
-- statement:
--   Let $n \ge 1$, $C \in \mathbb R^{n\times m}$ and $f \in \mathbb R^n$, and let $f^C \in \mathbb R^m$ be its $C$-transform, $(f^C)_j = \min_{i} C_{i,j} - f_i$. Then
--
--   1. $(f, f^C) \in \mathbf R(C)$, i.e. $f_i + (f^C)_j \le C_{i,j}$ for all $i, j$;
--   2. $f^C$ is the largest such vector: if $g \in \mathbb R^m$ satisfies $(f,g) \in \mathbf R(C)$, then $g \le f^C$ elementwise.
--
--   In words: once $f$ is frozen, $f^C$ is the best admissible choice of the second dual variable. This is the fact behind the semi-dual formulation (3.5).
--
--   **Formalization Note** The hypothesis $n \ge 1$ makes the minimum over $\llbracket n\rrbracket$ well defined; the book's index sets are nonempty throughout.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.2, p. 403, sentence following the definition of f^C

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- §3.2, p. 403: `(f, f^C) ∈ R(C)`, and `f^C` is the largest vector `g` with `(f, g) ∈ R(C)`.
The index set `⟦n⟧` is nonempty (`n ≥ 1`), so that `f^C` is a genuine minimum. -/
theorem sec_3_2_ctransform_admissible {n m : ℕ} (hn : 0 < n) (C : Matrix (Fin n) (Fin m) ℝ)
    (f : Fin n → ℝ) :
    dualFeasible C f (cTransform C f) ∧
      ∀ g : Fin m → ℝ, dualFeasible C f g → g ≤ cTransform C f := by sorry

end CompOT.Duality
