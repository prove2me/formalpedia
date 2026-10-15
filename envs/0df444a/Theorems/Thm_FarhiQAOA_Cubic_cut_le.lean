-- Prove2me | Theorems.Thm_FarhiQAOA_Cubic_cut_le
-- name    : FarhiQAOA.Cubic.cut_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:47.209117+00:00
-- url     : https://prove2.me/theorems/4e074b10-7cd6-4fc7-8688-fa2bab1f8be0
-- title:
--   Section V, p. 9 — every cut of a 3-regular graph has at most 3n/2 − S − T edges
-- statement:
--   Let $G$ be a 3-regular graph on $n$ vertices with $S$ crossed squares and $T$ isolated triangles. Then for every bit string $z$,
--   $$C(z) \le \frac{3n}{2} - S - T,$$
--   where $C(z)$ is the number of edges of $G$ cut by $z$.
--
--   A 3-regular graph has $3n/2$ edges, and each crossed square and each isolated triangle contains a triangle, at least one of whose edges is uncut. This upper bound on the maximum cut is the denominator of the approximation-ratio bound (34).
--
--   **Formalization Note** No connectivity hypothesis is needed and none is assumed.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 9, Section V, before (34)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann, Section V, p. 9: in a 3-regular graph on `n` vertices with `S` crossed
squares and `T` isolated triangles, every cut has at most `3n/2 − S − T` edges. -/
theorem cut_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) :
    ∀ z : Qubits n, cutValue G z ≤ (3 : ℝ) / 2 * (n : ℝ) - (S G : ℝ) - (T G : ℝ) := by sorry

end FarhiQAOA.Cubic
