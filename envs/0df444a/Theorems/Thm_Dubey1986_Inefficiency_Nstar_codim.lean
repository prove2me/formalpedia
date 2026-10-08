-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_Nstar_codim
-- name    : Dubey1986.Inefficiency.Nstar_codim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:39.780748+00:00
-- url     : https://prove2.me/theorems/519bfa8d-2ad9-4d7b-9a38-b140f18a0e87
-- title:
--   p. 4 — $N^*$ has codimension $r(n)$ in $\mathbb R^{n\times r(n)}$
-- statement:
--   For any block sizes $k(1),\dots,k(n)$ with $r(n)=\sum_i k(i)$, the linear subspace $N^*\subseteq\mathbb R^{n\times r(n)}$ has codimension $r(n)$:
--   $$\dim N^* + r(n) = n\cdot r(n).$$
--
--   This is the first clause of the dimension count on p. 4 that drives the finiteness of Nash equilibria: preimages of $N^*$ under a transverse map on the $r(n)$-dimensional $V$ are zero-dimensional.
--
--   **Formalization Note** The paper says "$N^*$ is a submanifold of codimension $r(n)$"; $N^*$ is a linear subspace, so the statement is a dimension identity. The second clause ($N^*\cap E^*$ is a finite union of submanifolds of codimension $\ge r(n)+1$) is not stated.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 4, last sentence, first clause

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

namespace Dubey1986.Inefficiency

theorem Nstar_codim {n : ℕ} (k : Fin n → ℕ) :
    Module.finrank ℝ (Nstar k) + ∑ i, k i = n * ∑ i, k i := by sorry

end Dubey1986.Inefficiency
