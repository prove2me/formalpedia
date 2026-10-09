-- Prove2me | Theorems.Thm_AffineVolterra_Transform_theorem_4_3
-- name    : AffineVolterra.Transform.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:48.699983+00:00
-- url     : https://prove2.me/theorems/900496f5-abc4-4c39-b58e-a12c22e4424e
-- title:
--   Theorem 4.3 — exponential-affine transform formula
-- statement:
--   Let $X$ be an affine Volterra process, fix a finite horizon $T$, a complex row $u$, and $f\in L^1([0,T])$. Suppose $\psi\in L^2([0,T])$ solves the Riccati–Volterra equation (4.3), and let $Y$ be the continuous adapted process defined by (4.4)–(4.5). Then, for each $t\le T$,
--
--   $$
--   Y_t=\mathbb E[uX_T+(f*X)_T\mid\mathcal F_t]+\tfrac12\int_t^T\psi(T-s)a(\mathbb E[X_s\mid\mathcal F_t])\psi(T-s)^\top\,ds.
--   $$
--
--   The process $e^{Y_t}$ is a complex local martingale on $[0,T]$. If it is a true martingale, then for each $t\le T$,
--
--   $$
--   \mathbb E\!\left[e^{uX_T+(f*X)_T}\mid\mathcal F_t\right]=e^{Y_t}.
--   $$
--
--   The result expresses the conditional Fourier–Laplace transform using a deterministic Riccati–Volterra solution and the process history.
--
--   **Formalization Note** Conditional identities are almost sure at each fixed time. The payoff and $X_s$ are asserted integrable as conclusions, so conditional expectations cannot take Lean's default zero for nonintegrable functions. A complex local martingale is represented by local martingality of its real and imaginary parts, stopped at $T$. In (4.6) the map $s\mapsto\mathbb E[X_s\mid\mathcal F_t]$ is taken as a jointly measurable version $m(s,\omega)$ (a conditional expectation is chosen separately for each $s$, so without this the $ds$-integral could be Lean's default zero); the statement asserts such a version exists and satisfies (4.6), and any two such versions give the same integral almost surely.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Theorem 4.3, p. 19, equations (4.3)–(4.7)

import Mathlib
import Definitions.Def_AffineVolterra_Transform_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace AffineVolterra.Transform

/-- Theorem 4.3, p. 19: (4.6), local martingality, and (4.7). In (4.6) the integrand uses a
jointly measurable version `m` of s ↦ E[X_s | ℱ_t]; any two such versions give the same
integral almost surely. -/
theorem theorem_4_3 {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (K : RKernel d) (D : AffineData d)
    (σ : State d → Matrix (Fin d) (Fin d) ℝ) (E : Set (State d))
    (x₀ : State d) (W X : ℝ≥0 → Ω → State d)
    (T : ℝ≥0) (u : CVec d) (f ψ : ℝ → CVec d)
    (Y : ℝ≥0 → Ω → ℂ)
    (hX : IsAffineVolterra P ℱ K D σ E x₀ W X)
    (hψ : IsRiccati43 K D T.val u f ψ)
    (hY : IsY43 P ℱ W X D σ x₀ T u f ψ Y) :
    Integrable (payoff u f X T) P ∧
    (∀ s : ℝ≥0, s ≤ T → Integrable (X s) P) ∧
    (∀ t : ℝ≥0, t ≤ T → ∃ m : ℝ → Ω → State d,
      Measurable (Function.uncurry m) ∧
      (∀ s : ℝ, t.val ≤ s → s ≤ T.val →
        m s =ᵐ[P] condExp (ℱ t) P (X s.toNNReal)) ∧
      ∀ᵐ ω ∂P,
        Y t ω = condExp (ℱ t) P (payoff u f X T) ω +
          (1 / 2 : ℂ) * ∫ s in t.val..T.val,
            quad (ψ (T.val - s)) (affA D (m s ω))) ∧
    EthierKurtz.IsSourceLocalMartingale P ℱ
      (fun t ω => (Complex.exp (Y (min t T) ω)).re) ∧
    EthierKurtz.IsSourceLocalMartingale P ℱ
      (fun t ω => (Complex.exp (Y (min t T) ω)).im) ∧
    (Martingale (fun t ω => Complex.exp (Y (min t T) ω)) ℱ P →
      ∀ t : ℝ≥0, t ≤ T → ∀ᵐ ω ∂P,
        condExp (ℱ t) P (fun ω => Complex.exp (payoff u f X T ω)) ω =
          Complex.exp (Y t ω)) := by sorry

end AffineVolterra.Transform
