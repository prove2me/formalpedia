-- Prove2me | Theorems.Thm_AffineVolterra_Existence_lemma_3_1
-- name    : AffineVolterra.Existence.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:16.176444+00:00
-- url     : https://prove2.me/theorems/2f4bd036-496a-4e61-927e-47a1bfe66851
-- title:
--   Lemma 3.1 — uniform moment bound for continuous solutions
-- statement:
--   Let $K$ have locally square-integrable matrix entries, and let $b$ and $\sigma$ be continuous coefficients obeying $\max\{|b(x)|,\|\sigma(x)\|\}\le c_{\mathrm{LG}}(1+|x|)$. Fix a finite horizon $T\ge0$, $p\ge2$, and a bound $R\ge0$ on the size of the deterministic initial condition. There is a finite constant $c$, depending only on $K|_{[0,T]},T,p,c_{\mathrm{LG}},R$, such that every continuous solution on any usual Brownian stochastic basis with $|x_0|\le R$ satisfies
--
--   $$
--   \sup_{0\le t\le T}\mathbb E[|X_t|^p]\le c.
--   $$
--
--   This is the a priori moment estimate used to control families of solutions with a common linear-growth bound.
--
--   **Formalization Note** The expectation is a nonnegative Lebesgue integral, so failure of integrability gives $+\infty$ rather than a default zero. Quantifying the constant before the probability space and coefficients records the paper's uniformity claim. The dependence on $K|_{[0,T]}$ is stated by letting the same constant serve every locally square-integrable kernel $K'$ that coincides with $K$ on $[0,T]$; the dependence on $|X_0|$ is read as uniformity over $|x_0|\le R$.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Lemma 3.1, p. 12

import Mathlib
import Definitions.Def_AffineVolterra_Existence_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AffineVolterra.Existence

/-- Lemma 3.1, p. 12: uniform moments of continuous solutions under linear growth.
The constant depends on the kernel only through its restriction to `[0, T]`: it serves
every locally square-integrable kernel `K'` that agrees with `K` there. -/
theorem lemma_3_1 {d m : ℕ} (K : Kernel d)
    (hK : ∀ i j, LpLoc 2 (fun t => K t i j))
    (T p cLG R : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ K' : Kernel d, (∀ i j, LpLoc 2 (fun t => K' t i j)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ T → K' t = K t) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
        (W : ℝ≥0 → Ω → State m) (X : ℝ≥0 → Ω → State d)
        (b : State d → State d) (σ : Diffusion d m) (x₀ : State d),
        IsUsualBasis P ℱ → IsFBrownian P ℱ W →
        Continuous b → Continuous σ → LinGrowth b σ cLG →
        ‖x₀‖ ≤ R → IsSolution P ℱ K' b σ x₀ W X →
        ∀ t : ℝ≥0, (t : ℝ) ≤ T →
          (∫⁻ ω, ENNReal.ofReal (‖X t ω‖ ^ p) ∂P) ≤ ENNReal.ofReal c := by sorry

end AffineVolterra.Existence
