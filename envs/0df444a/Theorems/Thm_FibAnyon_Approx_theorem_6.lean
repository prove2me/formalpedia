-- Prove2me | Theorems.Thm_FibAnyon_Approx_theorem_6
-- name    : FibAnyon.Approx.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:27.544758+00:00
-- url     : https://prove2.me/theorems/d31767b1-9673-4469-8d5b-28f157b7a0c6
-- title:
--   Theorem 6, p. 5 — exact synthesis correctness and circuit-length bounds
-- statement:
--   For every exact unitary $U[u,v,k]$, the circuit returned by the Figure 4 synthesis loop evaluates exactly to $U[u,v,k]$. There are positive absolute constants $K_1,K_2$ such that every circuit $C$ implementing this unitary and the returned circuit $C_{\rm alg}$ satisfy
--
--   $$\log G(u)\le K_1\,\operatorname{length}(C)+K_1,\qquad \operatorname{length}(C_{\rm alg})\le K_2\log G(u)+K_2.$$
--
--   Thus the algorithm terminates with the right matrix and has logarithmic output length, while any implementation requires length proportional to the same logarithm up to additive constants.
--
--   **Formalization Note** The $\omega I$ gate is permitted and has zero counted length. This item states Theorem 6's matrix correctness and both directions of its length estimate. It leaves the arithmetic-operation count in part 3 outside the mission's cost model.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, p. 5, Theorem 6, parts 1–2 and output-length clause of part 3

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace FibAnyon.Approx

/-- Theorem 6, p. 5: correctness and the two sides of the length estimate. -/
theorem theorem_6 :
    (∀ (u v : ZOmega) (k : ℤ), IsExact u v →
      circuitMat (exactSynthesize u v k) = exactU u v k) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (u v : ZOmega) (k : ℤ), IsExact u v →
      ∀ C : List Gate, circuitMat C = exactU u v k →
        Real.log (gaussG u) ≤ K * (circuitLength C : ℝ) + K) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (u v : ZOmega) (k : ℤ), IsExact u v →
      (circuitLength (exactSynthesize u v k) : ℝ) ≤
        K * Real.log (gaussG u) + K) := by sorry

end FibAnyon.Approx
