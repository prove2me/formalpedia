-- Prove2me | Theorems.Thm_BregmanPPA_Convergence_step2
-- name    : BregmanPPA.Convergence.step2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:21:33.786095+00:00
-- url     : https://prove2.me/theorems/bc6fc62c-2032-4bcd-a196-3440253a98d6
-- title:
--   Theorem 1, Step 2 — every limit point is a zero
-- statement:
--   Let $T$, $S$, $h$, $(c_k)$, and $(x^k)$ satisfy the standing hypotheses of Theorem 1, and assume either (C1), $\overline{\operatorname{dom}T}\subseteq S$, or (C2), $T=\partial f$ for a proper lower semicontinuous convex function $f$. Suppose $T$ has a zero. Every subsequential limit $x^*$ of $(x^k)$ is a zero of $T$:
--
--   $$x^{k(j)}\to x^*\quad\Longrightarrow\quad 0\in T(x^*).$$
--
--   This identifies all possible accumulation points before whole-sequence convergence is established.
--
--   **Formalization Note** A subsequence has strictly increasing natural-number indices. The standing hypotheses include $\operatorname{dom}T\subseteq\overline S$, $c_k>0$ with a positive uniform lower bound, and the inclusion form (4) of the run.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 207–208, Theorem 1 proof, Step 2, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology

namespace BregmanPPA.Convergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1, proof, Step 2: every subsequential limit is a zero. -/
theorem step2 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f)
    (hz : (zer T).Nonempty) :
    ∀ (x' : H) (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∈ zer T := by sorry

end BregmanPPA.Convergence
