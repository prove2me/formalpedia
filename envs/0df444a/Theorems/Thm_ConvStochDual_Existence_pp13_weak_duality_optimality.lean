-- Prove2me | Theorems.Thm_ConvStochDual_Existence_pp13_weak_duality_optimality
-- name    : ConvStochDual.Existence.pp13_weak_duality_optimality
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T03:07:22.944955+00:00
-- url     : https://prove2.me/theorems/175a0d59-9c3b-4e7c-95a1-81e86b772a66
-- title:
--   Weak duality and scenario-wise optimality conditions for (SP) — Lemma 21 / Theorem 26 of Pennanen–Perkkiö (2022)
-- statement:
--   Consider the stochastic program and its dual from Pennanen–Perkkiö: $f$ is a convex normal integrand on $\mathbb R^n\times\mathbb R^m\times\Omega$, $\bar u\in\mathcal U$, $Ef(x,u)=\mathbb E[f(x(\omega),u(\omega),\omega)]$ (with the convention that the integral is $+\infty$ unless the positive part is integrable), and the dual objective is
--
--   $$(p,y)\mapsto \langle \bar u,y\rangle-Ef^*(p,y),\qquad (p,y)\in\mathcal X_a^\perp\times\mathcal Y,$$
--
--   where $f^*(\cdot,\cdot,\omega)$ is the pointwise convex conjugate of $f(\cdot,\cdot,\omega)$ and $\mathcal X_a^\perp\subseteq\mathcal V$ is the annihilator of the adapted strategies $\mathcal X_a$. Assume the standing assumptions of the paper (Fréchet spaces of random variables in separating duality, decomposable and solid, a filtration, a normal integrand $f$). Let $x\in L^0$ be an adapted strategy, $p\in\mathcal X_a^\perp$ and $y\in\mathcal Y$. Then:
--
--   1. (weak duality) $\langle\bar u,y\rangle-Ef^*(p,y)\le Ef(x,\bar u)$;
--   2. if $Ef(x,\bar u)$ is finite and $\langle\bar u,y\rangle-Ef^*(p,y)=Ef(x,\bar u)$, then $(p,y)\in\partial f(x,\bar u)$ almost surely, i.e. $f(x(\omega),\bar u(\omega),\omega)$ is finite and
--   $$f(x',u',\omega)\ge f(x(\omega),\bar u(\omega),\omega)+(x'-x(\omega))\cdot p(\omega)+(u'-\bar u(\omega))\cdot y(\omega)\quad\forall x',u';$$
--   3. if $Ef(x,\bar u)<\infty$ and $(p,y)\in\partial f(x,\bar u)$ almost surely, then $x$ solves $(SP)$: $Ef(x,\bar u)\le Ef(x',\bar u)$ for every adapted $x'$.
--
--   Item 1 is the inequality following Lemma 21 of the source (the duality gap between $(SP)$ and $(D)$ is nonnegative), and items 2–3 are the two directions of the equivalence in Theorem 26 of the source. Together with dual attainment and absence of a duality gap they give the scenario-wise optimality conditions of Corollary 27.
--
--   **Formalization Note** In item 3 the dual feasibility of $(p,y)$ assumed in the source is not needed and is dropped; feasibility of $x$ is expressed as $Ef(x,\bar u)<\infty$.
-- source:
--   T. Pennanen and A.-P. Perkkiö, Duality in convex stochastic optimization, arXiv:2205.02045v1, p. 16 (display after Lemma 21 / Corollary 23: inf(SP) ≥ dual objective) and p. 17, Theorem 26 (1⇔2); cited as [13, Corollary 27] in the proof of Theorem 27 of arXiv:2205.15825v1, p. 20

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting

open MeasureTheory

namespace ConvStochDual.Existence

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

/-- Pennanen–Perkkiö, Duality in convex stochastic optimization, arXiv:2205.02045v1,
p. 16, Lemma 21 (weak duality between (SP) and (D)) and p. 17, Theorem 26
(scenario-wise optimality conditions), in the setting of arXiv:2205.15825v1. -/
theorem pp13_weak_duality_optimality (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (x : RV Ω P n) (hx : Adapted τ 𝔽 P x)
    (p : V) (hp : p ∈ XaPerp s) (y : Y) :
    dualObj s p y ≤ Ef s x (ιU s.ubar) ∧
    (Ef s x (ιU s.ubar) ≠ ⊤ → Ef s x (ιU s.ubar) ≠ ⊥ →
      dualObj s p y = Ef s x (ιU s.ubar) →
      ∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω) (p.1 ω) (y.1 ω)) ∧
    (Ef s x (ιU s.ubar) < ⊤ →
      (∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω) (p.1 ω) (y.1 ω)) →
      ∀ x' : RV Ω P n, Adapted τ 𝔽 P x' → Ef s x (ιU s.ubar) ≤ Ef s x' (ιU s.ubar)) := by sorry

end ConvStochDual.Existence
