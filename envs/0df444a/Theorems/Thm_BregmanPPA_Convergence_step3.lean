-- Prove2me | Theorems.Thm_BregmanPPA_Convergence_step3
-- name    : BregmanPPA.Convergence.step3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:21:42.704152+00:00
-- url     : https://prove2.me/theorems/9bc4dddc-853f-444e-a7f9-6bc1323335d8
-- title:
--   Theorem 1, Step 3 — convergence to the zero limit point
-- statement:
--   Under the standing hypotheses and either (C1) or (C2) of Theorem 1, suppose a subsequence of the Bregman proximal-point run converges to a zero $x^*$ of $T$. Then the entire run converges to that point:
--
--   $$x^{k(j)}\to x^*,\quad 0\in T(x^*)\quad\Longrightarrow\quad x^k\to x^*.$$
--
--   This rules out a second limit point and completes the convergence half of Theorem 1 once Step 2 has identified a zero limit point.
--
--   **Formalization Note** The subsequence indices are strictly increasing. The conclusion is convergence of the whole sequence.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 208, Theorem 1 proof, Step 3, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology

namespace BregmanPPA.Convergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1, proof, Step 3: a zero attained as a limit point attracts the whole run. -/
theorem step3 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f)
    (x' : H) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 x')) (hzero : x' ∈ zer T) :
    Tendsto x atTop (𝓝 x') := by sorry

end BregmanPPA.Convergence
