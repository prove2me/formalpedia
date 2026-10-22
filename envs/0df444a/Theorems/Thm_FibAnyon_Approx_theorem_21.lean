-- Prove2me | Theorems.Thm_FibAnyon_Approx_theorem_21
-- name    : FibAnyon.Approx.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:34.76376+00:00
-- url     : https://prove2.me/theorems/6d1ccab6-a819-4a6b-9810-1518898f6f60
-- title:
--   Theorem 21, p. 14 (corrected Figures 12–13) — every Rz output meets precision and length
-- statement:
--   There is an absolute constant $K>0$ such that, for every real angle $\phi$ and $0<\varepsilon\le1/2$, every valid angle-reduction integer $k$, every allowed sample index $j$, and every solution $x\in\mathbb Z[\omega]$ of Figure 12's norm equation, the circuit $C$ returned by the corrected approximation algorithm satisfies
--
--   $$d(C,R_z(\phi))\le\varepsilon,\qquad \operatorname{length}(C)\le K\log(1/\varepsilon).$$
--
--   The assertion covers each possible output of the algorithm. It does not claim that a successful norm-equation sample exists or that the sampler terminates; the paper's average-runtime assertion is conditional on Conjecture 20.
--
--   **Formalization Note** The algorithm uses $U[u,v,5]$ at the final synthesis step and the corrected sign in Figure 13's $x_{\max}$. The theorem quantifies over every norm-equation solution and sample index; EASY-SOLVABLE is dropped because it restricts which samples are kept but does not change the output guarantee. The range $0<\varepsilon\le1/2$ fixes the asymptotic regime and excludes total-function boundary values.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, p. 14, Theorem 21, first sentence; Figures 12–13 (corrected)

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace FibAnyon.Approx

/-- Theorem 21, p. 14, first sentence, for every output of corrected Figures 12–13. -/
theorem theorem_21 :
    ∃ K : ℝ, 0 < K ∧ ∀ (φ ε : ℝ), 0 < ε → ε ≤ 1/2 →
      ∀ k : ℤ, 0 ≤ rzTheta φ k → rzTheta φ k ≤ Real.pi/5 →
      ∀ j : ℕ, 1 ≤ j → j ≤ sampleN ε 1 - 1 →
      ∀ x : ZOmega, x * x.conj = rzXi φ ε k j →
        dist (circuitMat (rzOutput φ ε k j x)) (Rz φ) ≤ ε ∧
        (circuitLength (rzOutput φ ε k j x) : ℝ) ≤
          K * Real.log (1/ε) := by sorry

end FibAnyon.Approx
