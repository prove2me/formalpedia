-- Prove2me | Theorems.Thm_AutomorphicForm_RealIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero
-- name    : AutomorphicForm.RealIwasawa.exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/93ddcd05-aa54-5225-95e8-88c95f8b21a9
-- title:
--   Entire continuation of the real weight–Fourier integral for t ≠ 0
-- statement:
--   Fix an integer $k$, and let $j$ be the function of a complex exponent $w$ and a real frequency $t$ given by the integral over $x \in \mathbb{R}$ of $\bigl((x - i)/\sqrt{1+x^2}\bigr)^{k}\,(1+x^2)^{-w}\,e^{-2\pi i t x}$ (the Bochner integral in $\mathbb{C}$, with the complex power $(1+x^2)^{-w}$ and the integer power $k$). The assertion is the existence of a function $J : \mathbb{C} \times \mathbb{R} \to \mathbb{C}$ (formally $J : \mathbb{C} \to \mathbb{R} \to \mathbb{C}$) with four properties: for every $t \neq 0$ the function $w \mapsto J(w,t)$ is analytic on a neighbourhood of every point of $\mathbb{C}$, i.e. entire; for every $w$ with $\operatorname{Re} w > 1/2$ and every $t \neq 0$ one has $J(w,t) = j(w,t)$, so $J$ continues $j$ from that half-plane; the map $(w,t) \mapsto J(w,t)$ is continuous on $\mathbb{C} \times (\mathbb{R} \setminus \{0\})$; and for every compact $K \subseteq \mathbb{C}$ there is an exponent $A \in \mathbb{N}$, depending only on $K$, such that for every $N \in \mathbb{N}$ there is $C > 0$ with $\|J(w,t)\| \le C\,\max(1,|t|^{-1})^{A}\,(1+|t|)^{-N}$ for all $w \in K$ and all $t \neq 0$.
--
--   This is the archimedean weight–Fourier (Whittaker) integral attached to the Iwasawa decomposition at a real place: for non-zero frequency it is entire in the exponent, with rapid decay as $|t| \to \infty$ uniformly on compacta and at worst polynomial blow-up as $t \to 0$. It is the continuation-in-the-exponent counterpart of the half-plane statement [`AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral`](thm.html#AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral), and is used in the analysis of Whittaker coefficients of flat families of automorphic forms, where the archimedean factor must be separated from the Euler product as an entire function with controlled growth.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RealIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem AutomorphicForm.RealIwasawa.exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero (k : ℤ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → AnalyticOnNhd ℂ (fun w : ℂ => J w t) Set.univ) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 → J w t = j w t) ∧
      ContinuousOn (fun p : ℂ × ℝ => J p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) ∧
      (∀ K : Set ℂ, IsCompact K → ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖J w t‖ ≤ C * (max 1 |t|⁻¹) ^ A * (1 + |t|) ^ (-(N : ℝ))) := by sorry
