-- Prove2me | Theorems.Thm_AutomorphicForm_RealIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
-- name    : AutomorphicForm.RealIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/bdac1c0b-d4fe-5aa7-a9a8-00413cfb7fce
-- title:
--   Entire continuation of the weight-k archimedean Whittaker integral
-- statement:
--   Fix an integer $k$ and write, for $w \in \mathbb{C}$ and $t \in \mathbb{R}$,
--   $$j(w,t) = \int_{\mathbb{R}} \left(\frac{x - i}{\sqrt{1+x^{2}}}\right)^{k} (1+x^{2})^{-w} \, e^{-2\pi i t x}\, dx,$$
--   where the $k$-th power is an integer power of a complex number, $(1+x^{2})^{-w}$ is the complex power of the positive real $1+x^{2}$, and the integral is the Bochner integral in $x$ over $\mathbb{R}$ with respect to Lebesgue measure (so it is given the value $0$ at those $(w,t)$ for which the integrand fails to be integrable). The assertion is that there exists a function $J : \mathbb{C} \times \mathbb{R} \to \mathbb{C}$, written $J(w,t)$, with four properties: for every real $t \neq 0$ the function $w \mapsto J(w,t)$ is complex differentiable on all of $\mathbb{C}$; $J(w,t) = j(w,t)$ whenever $\operatorname{Re} w > 1/2$ and $t \neq 0$; the map $(w,t) \mapsto J(w,t)$ is continuous on $\mathbb{C} \times \{t \in \mathbb{R} : t \neq 0\}$; and for every compact $K \subseteq \mathbb{C}$ there is an $M \in \mathbb{N}$ such that for every $N \in \mathbb{N}$ there is a constant $C > 0$ with $\|J(w,t)\| \le C\,|t|^{-M}(1+|t|)^{-N}$ for all $w \in K$ and all real $t \neq 0$. Note that $M$ is chosen before, and hence uniformly in, $N$.
--
--   This is the archimedean Whittaker (Jacquet) integral attached to a weight-$k$ vector in a principal series of $\mathrm{GL}_2(\mathbb{R})$, continued from the half-plane $\operatorname{Re} w > 1/2$ of absolute convergence to the whole $w$-plane at each non-zero frequency $t$, with rapid decay as $|t| \to \infty$ and at most polynomial blow-up as $t \to 0$, locally uniformly in $w$. It feeds the continuation of Whittaker coefficients of a flat family of unitary automorphic forms, via [`AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary`](thm.html#AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary); the convergence, continuity and rapid-decay statements in the half-plane come from [`AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral`](thm.html#AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RealIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem AutomorphicForm.RealIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay (k : ℤ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => J w t)) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 → J w t = j w t) ∧
      ContinuousOn (fun p : ℂ × ℝ => J p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) ∧
      (∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖J w t‖ ≤ C * |t| ^ (-(M : ℝ)) * (1 + |t|) ^ (-(N : ℝ))) := by sorry
