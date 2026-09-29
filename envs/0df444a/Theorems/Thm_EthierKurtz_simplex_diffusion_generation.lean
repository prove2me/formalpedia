-- Prove2me | Theorems.Thm_EthierKurtz_simplex_diffusion_generation
-- name    : EthierKurtz.simplex_diffusion_generation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:17:21.211405+00:00
-- url     : https://prove2.me/theorems/e842988d-073c-45d4-83eb-46863a96f4a8
-- title:
--   Theorem 2.8 — simplex diffusion generation and polynomial core
-- statement:
--   For every positive dimension and every globally Lipschitz drift that points inward on every coordinate face and has nonpositive total component on the top face, the closure of the C² simplex diffusion graph is single-valued and is exactly the generator of a positive conservative strongly continuous contraction semigroup on C(K_d); polynomial restrictions form a core for that generator.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 2, Theorem 2.8, printed p. 375 (PDF p. 384); operator equation (1.15), printed p. 368 (PDF p. 377); generator/core and Feller conventions on printed pp. 17 and 166; Appendix 6 C² extension convention on printed pp. 499–500.

import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_WFState
import Definitions.Def_EthierKurtz_simplexDiffusionGraph

open Filter
open scoped Topology BigOperators ContDiff NNReal
namespace EthierKurtz

/-- Full simplex generation theorem, including the polynomial core.
The supremum norm on finite-coordinate vectors is equivalent to the Euclidean
norm, so existence of a Lipschitz constant has exactly the source meaning. -/
theorem simplex_diffusion_generation (d : ℕ) (hd : 0 < d)
    (b : WFState d → Fin d → ℝ)
    (hLipschitz : ∃ L : ℝ≥0, LipschitzWith L b)
    (hfaces : ∀ x : WFState d, ∀ i : Fin d, x.val i = 0 → 0 ≤ b x i)
    (htop : ∀ x : WFState d, (∑ i, x.val i) = 1 → (∑ i, b x i) ≤ 0) :
    let graph := simplexDiffusionGraph b
    let A := closure graph
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    (∃ T : ℝ → BoundedContinuousFunction (WFState d) ℝ →L[ℝ]
        BoundedContinuousFunction (WFState d) ℝ,
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A)) ∧
    closure {fg : BoundedContinuousFunction (WFState d) ℝ ×
        BoundedContinuousFunction (WFState d) ℝ |
      fg ∈ graph ∧ ∃ p : MvPolynomial (Fin d) ℝ,
        ∀ x : WFState d, fg.1 x = MvPolynomial.eval x.val p} = A := by sorry
