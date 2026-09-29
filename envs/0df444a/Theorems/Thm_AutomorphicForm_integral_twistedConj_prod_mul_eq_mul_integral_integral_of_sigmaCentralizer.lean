-- Prove2me | Theorems.Thm_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
-- name    : AutomorphicForm.integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/1f81b534-ad8d-5b7c-9391-09438524b657
-- title:
--   Twisted orbital integrals over a product of groups
-- statement:
--   Let $G_1,G_2$ be second-countable, locally compact, Hausdorff topological groups, each carrying its Borel $\sigma$-algebra, let $\theta_i\colon G_i\to G_i$ be continuous endomorphisms and $\delta_i\in G_i$. Let $\mu$ be a Haar measure on $G_1\times G_2$, $\mu_i$ Haar measures on $G_i$, and let $\tau_i$ be Haar measures on the twisted centraliser $\{t\in G_i: t\delta_i(\theta_i t)^{-1}=\delta_i\}$ which are in addition invariant under inversion. Let $e$ be a map from the product of these two twisted centralisers to the twisted centraliser of $\theta_1\times\theta_2$ at $(\delta_1,\delta_2)$ whose underlying map to $G_1\times G_2$ is $(t_1,t_2)\mapsto(t_1,t_2)$. Then there exists a real $c>0$, independent of all data below, with the following property. Let $f\colon G_1\times G_2\to\mathbb{C}$ be continuous and bounded, and let $W_i\colon G_i\to\mathbb{R}$ be continuous, non-negative and compactly supported, such that $\int W_i(tx_i)\,d\tau_i=1$ whenever $f(x_1^{-1}\delta_1\theta_1x_1,x_2^{-1}\delta_2\theta_2x_2)\neq0$. Write $\tau$ for the image of $\tau_1\otimes\tau_2$ under $e$. Then (1) $\int W_1((tx)_1)W_2((tx)_2)\,d\tau=1$ for every $x$ with $f(x^{-1}(\delta_1,\delta_2)(\theta_1\times\theta_2)(x))\neq0$; and (2) for every non-negative, Borel measurable, compactly supported $w\colon G_1\times G_2\to\mathbb{R}$ with $\int w(tx)\,d\tau=1$ at all such $x$, $$\int f\bigl(x^{-1}(\delta_1,\delta_2)(\theta_1\times\theta_2)(x)\bigr)w(x)\,d\mu=c\int\!\!\int f(x_1^{-1}\delta_1\theta_1x_1,x_2^{-1}\delta_2\theta_2x_2)W_1(x_1)W_2(x_2)\,d\mu_2\,d\mu_1.$$
--
--   This is the step that peels off one place in the assembly of (twisted) orbital integrals over a product of groups: the weighted orbital integral on $G_1\times G_2$ is rewritten as an iterated integral with product weight $W_1\otimes W_2$, the constant $c$ being the Haar comparison factor between $\mu$ and $\mu_1\otimes\mu_2$. The independence of the left-hand side from the choice of normalised weight $w$ comes from [`AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one`](thm.html#AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one); the result is used by [`AutomorphicForm.semilocal_central_transfer_peel_step`](thm.html#AutomorphicForm.semilocal_central_transfer_peel_step) and [`AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step`](thm.html#AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer.lean

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

theorem AutomorphicForm.integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
    {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [SecondCountableTopology G₂] [T2Space G₂]
    (θ₁ : G₁ →* G₁) (hθ₁ : Continuous θ₁) (θ₂ : G₂ →* G₂) (hθ₂ : Continuous θ₂) (δ₁ : G₁) (δ₂ : G₂)
    (μ : @Measure (G₁ × G₂) (borel (G₁ × G₂))) (hμ : @Measure.IsHaarMeasure (G₁ × G₂) _ _ (borel _) μ)
    (μ₁ : @Measure G₁ (borel G₁)) (hμ₁ : @Measure.IsHaarMeasure G₁ _ _ (borel G₁) μ₁)
    (μ₂ : @Measure G₂ (borel G₂)) (hμ₂ : @Measure.IsHaarMeasure G₂ _ _ (borel G₂) μ₂)
    (τ₁ : @Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁) (hτ₁i : @Measure.IsInvInvariant _ (borel _) _ τ₁)
    (τ₂ : @Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _))
    (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂) (hτ₂i : @Measure.IsInvInvariant _ (borel _) _ τ₂)
    (e : AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂ →
      AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂))
    (he : ∀ p, ((e p : AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) : G₁ × G₂) =
      ((p.1 : G₁), (p.2 : G₂))) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (f : G₁ × G₂ → ℂ), Continuous f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      ∀ (W₁ : G₁ → ℝ) (W₂ : G₂ → ℝ), Continuous W₁ → (∀ x, 0 ≤ W₁ x) → HasCompactSupport W₁ →
        Continuous W₂ → (∀ x, 0 ≤ W₂ x) → HasCompactSupport W₂ →
        (∀ (x₁ : G₁) (x₂ : G₂), f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : G₁) * x₁)) = 1 ∧
          @integral _ ℝ _ _ (borel _) τ₂ (fun t => W₂ ((t : G₂) * x₂)) = 1) →
        letI τ : @Measure (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) (borel _) :=
          @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) e
            (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)
        (∀ x : G₁ × G₂, f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ
              (fun t => W₁ (((t : G₁ × G₂) * x).1) * W₂ (((t : G₁ × G₂) * x).2)) = 1) ∧
        (∀ w : G₁ × G₂ → ℝ, (∀ x, 0 ≤ w x) → Measurable[borel (G₁ × G₂)] w → HasCompactSupport w →
          (∀ x : G₁ × G₂, f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ (fun t => w ((t : G₁ × G₂) * x)) = 1) →
          @integral _ ℂ _ _ (borel (G₁ × G₂)) μ (fun x => f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) * (w x : ℂ)) =
            ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel G₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel G₂) μ₂ (fun x₂ =>
              f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) * ((W₁ x₁ * W₂ x₂ : ℝ) : ℂ)))) := by sorry
