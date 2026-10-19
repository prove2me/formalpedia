-- Prove2me | Theorems.Thm_DROCalibration_Sensitivity_proposition_F_1_form
-- name    : DROCalibration.Sensitivity.proposition_F_1_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:17.365036+00:00
-- url     : https://prove2.me/theorems/a2a6e681-ac17-4c3c-8922-1f2d576fc270
-- title:
--   Proposition F.1, (F.1)–(F.2), p. 47 — for small δ > 0 the worst-case distribution is unique, q_i = p_i [φ′]⁻¹(δ[−f_i − c⋆(δ)])
-- statement:
--   Fix a decision $x$, nominal probabilities $p_i>0$ with $\sum_i p_i=1$ (the empirical distribution is $p_i=1/n$) and rewards $f_i=f(x,Y_i)$. Let $\phi$ satisfy Assumption 2.1 and let $\phi^*$ be its convex conjugate. Then there are $\delta_0>0$ and $r>0$ such that for every $\delta\in(0,\delta_0)$ there are a number $c=c^\star(\delta)$ and a probability vector $q^*=q^*(\delta)$ with:
--
--   1. $q^*$ is the **unique** minimizer of $\sum_i q_if_i+\frac1\delta\sum_ip_i\phi(q_i/p_i)$ over the probability simplex, i.e. $\mathbb Q(\delta)=q^*$ in (2.7);
--   2. for every $i$, $q^*_i/p_i\in(1-r,1+r)$ and it is the unique point of that interval with
--   $$\phi'\!\left(\frac{q^*_i}{p_i}\right)=\delta(-f_i-c),\qquad\text{i.e. } q_i^*=p_i\,[\phi']^{-1}\big(\delta(-f_i-c)\big)\quad\text{(F.1)–(F.2)};$$
--   3. $c$ maximizes the dual function
--   $$c'\mapsto-\frac1\delta\sum_{i=1}^n p_i\,\phi^*\big(\delta(-f_i-c')\big)-c'$$
--   over $c'\in\mathbb R$ (the second line of (F.2)).
--
--   This gives the closed form of the worst-case distribution of the penalized distributionally robust problem for small $\delta$, which is the starting point of the expansion (F.3).
--
--   **Formalization Note** The local inverse $[\phi']^{-1}$ is encoded by the window $(1-r,1+r)$ and the uniqueness clause; $\phi'$ is the derivative of the real part of $\phi$. The dual function is evaluated in `EReal`, where it takes the value $-\infty$ whenever some $\phi^*(\delta(-f_i-c'))=+\infty$.
-- source:
--   Gotoh, Kim & Lim, Calibration of Distributionally Robust Empirical Optimization Models, arXiv:1711.06565v2, p. 47, Proposition F.1, (F.1)–(F.2)

import Mathlib
import Definitions.Def_DROCalibration_Sensitivity_Setting

open Filter Topology

namespace DROCalibration.Sensitivity

theorem proposition_F_1_form (φ : ℝ → EReal) (hφ : Assumption21 φ) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (f : Fin n → ℝ) :
    ∃ δ₀ > 0, ∃ r > 0, ∀ δ ∈ Set.Ioo 0 δ₀, ∃ c : ℝ, ∃ q ∈ stdSimplex ℝ (Fin n),
      worstCaseSet φ p f δ = {q} ∧
      (∀ i, q i / p i ∈ Set.Ioo (1 - r) (1 + r) ∧
        deriv (phiReal φ) (q i / p i) = δ * (-f i - c) ∧
        ∀ y ∈ Set.Ioo (1 - r) (1 + r), deriv (phiReal φ) y = δ * (-f i - c) → y = q i / p i) ∧
      IsMaxOn (fun c' : ℝ => -(((δ⁻¹ : ℝ) : EReal) *
          ∑ i, ((p i : ℝ) : EReal) * conj φ (δ * (-f i - c'))) - (c' : EReal)) Set.univ c := by sorry

end DROCalibration.Sensitivity
