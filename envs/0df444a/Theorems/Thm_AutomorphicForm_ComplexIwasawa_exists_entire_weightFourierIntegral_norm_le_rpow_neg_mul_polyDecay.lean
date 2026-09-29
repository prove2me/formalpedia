-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
-- name    : AutomorphicForm.ComplexIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a6df7244-636a-5f6c-9248-411b5600fa94
-- title:
--   Entire continuation and decay of the complex-place Jacquet integral
-- statement:
--   Fix natural numbers $a$ and $b$, and let $j(w,\zeta)$ denote the Bochner integral over $\mathbb{C}$ with respect to Lebesgue measure $$j(w,\zeta)=\int_{\mathbb{C}} z^{a}\,\overline{z}^{\,b}\,\bigl(1+\lVert z\rVert^{2}\bigr)^{-w}\,\exp\!\bigl(-4\pi i\,\operatorname{Re}(\zeta z)\bigr)\,dz,$$ where the factor $(1+\lVert z\rVert^{2})^{-w}$ uses the complex power of the positive real number $1+\lVert z\rVert^{2}$. The assertion is that there exists a function $J:\mathbb{C}\to\mathbb{C}\to\mathbb{C}$ with four properties: first, for every $\zeta\neq 0$ the map $w\mapsto J(w,\zeta)$ is complex differentiable on all of $\mathbb{C}$; second, $J(w,\zeta)=j(w,\zeta)$ whenever $(a+b)/2+1<\operatorname{Re} w$ and $\zeta\neq 0$; third, $(w,\zeta)\mapsto J(w,\zeta)$ is continuous on the product set $\mathbb{C}\times\{\zeta:\zeta\neq0\}$; and fourth, for every compact $K\subseteq\mathbb{C}$ there is a natural number $M$ such that for every natural number $N$ there is a real constant $C>0$ with $\lVert J(w,\zeta)\rVert\le C\,\lVert\zeta\rVert^{-M}(1+\lVert\zeta\rVert)^{-N}$ for all $w\in K$ and all $\zeta\neq 0$. Note that $K$ is an arbitrary compact subset of the plane, not constrained to the half-plane of absolute convergence, that $M$ depends only on $K$, and that $N$ may be taken arbitrarily large.
--
--   This is the whole-plane continuation, in the spectral parameter, of the archimedean Jacquet (Whittaker) integral of a $K$-type vector for a principal series of $\mathrm{GL}_2(\mathbb{C})$, together with rapid decay in the frequency $\zeta$ at infinity and at most polynomial blow-up as $\zeta\to0$, locally uniformly in the parameter. Its input on the half-plane $\operatorname{Re} w>(a+b)/2+1$ — joint continuity, holomorphy in $w$, and the decay bound $C(1+\lVert\zeta\rVert)^{-N}$ — is [`AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral`](thm.html#AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral), and it feeds the continuation of Whittaker coefficients in [`AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary`](thm.html#AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem AutomorphicForm.ComplexIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay (a b : ℕ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w : ℂ) (ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 → J w ζ = j w ζ) ∧
      ContinuousOn (fun p : ℂ × ℂ => J p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) ∧
      (∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖J w ζ‖ ≤ C * ‖ζ‖ ^ (-(M : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ))) := by sorry
