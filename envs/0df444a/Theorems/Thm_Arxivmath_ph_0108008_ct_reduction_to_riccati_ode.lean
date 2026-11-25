-- Prove2me | Theorems.Thm_Arxivmath_ph_0108008_ct_reduction_to_riccati_ode
-- name    : Arxivmath_ph_0108008.ct_reduction_to_riccati_ode
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:34:58.488566+00:00
-- url     : https://prove2.me/theorems/e81dad02-1fe9-4e58-abdf-6815818ea813
-- title:
--   Section 2, first paragraph: for $S=\{0\}$, $T=\{2\}$, $\gamma_0=-6$, $g=-6g_0$, and every solution of (1.1) solves $h''+h=6s^{-2}h$
-- statement:
--   Let $u_m,v_m$ be families with $u_0=\sin$, $v_0=-\cos$, and take $S=\{0\}$, $T=\{2\}$. Then:
--   1. Eq. (1.2) holds if and only if $\gamma_0=-6$.
--   2. In that case the kernel is $g(s,t)=-6g_0(s,t)$, where $g_0(s,t)=-\sin(\min(s,t))\cos(\max(s,t))$.
--   3. $g_0$ is a Green's function of $d^2+1$, i.e. $(d^2+1)g_0=\delta(s-t)$. Precisely: for $r>0$ and $f$ continuous on $[0,r]$, $w(s)=\int_0^r g_0(s,t)f(t)\,dt$ is twice differentiable on $(0,r)$ and $w''+w=f$ there.
--   4. Every solution $h$ of (1.1) on $[0,r]$ (in the sense of the definitions) is twice differentiable on $(0,r)$ and satisfies $h''(s)+h(s)=6s^{-2}h(s)$ there.
--   5. $u_2(s)=(3s^{-2}-1)\sin s-3s^{-1}\cos s$ solves this equation for $s>0$, tends to $0$ as $s\to0^+$, and is not identically zero.
--   6. Every solution of the equation on $(0,r)$ that tends to $0$ as $s\to0^+$ is a constant multiple $c\,u_2$.
--
--   **Formalization Note** The paper states $(d^2+1)g_0=\delta(s-t)$ in distributional language; item 3 is the classical meaning of this identity for continuous right-hand sides. "Nontrivial solution regular at zero, $c\,u_2$" is items 5 and 6. Regularity at $0$ is read as $h(s)\to0$, which is how the solution of (1.1) behaves since $h(0)=0$. This step gives only a necessary condition: it does not show that $u_2$ solves (1.1). That is the content of `ct_integral_of_u2` and `ct_nontrivial_solution`.
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1, claim c008; Section 2, first paragraph, with Eqs. (1.1)-(1.2), PDF p. 2

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

namespace Arxivmath_ph_0108008

theorem ct_reduction_to_riccati_ode (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) :
    (∀ γ : ℝ → ℝ, CTCoeffEq {0} {2} γ ↔ γ 0 = -6) ∧
    (∀ γ : ℝ → ℝ, CTCoeffEq {0} {2} γ → ∀ s t : ℝ, ctKernel u v {0} γ s t = -6 * greenG0 s t) ∧
    (∀ r : ℝ, 0 < r → ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 r) → ∀ s ∈ Set.Ioo 0 r,
      DifferentiableAt ℝ (fun x => ∫ t in (0 : ℝ)..r, greenG0 x t * f t) s ∧
      DifferentiableAt ℝ (deriv (fun x => ∫ t in (0 : ℝ)..r, greenG0 x t * f t)) s ∧
      deriv (deriv (fun x => ∫ t in (0 : ℝ)..r, greenG0 x t * f t)) s +
        (∫ t in (0 : ℝ)..r, greenG0 s t * f t) = f s) ∧
    (∀ γ : ℝ → ℝ, CTCoeffEq {0} {2} γ → ∀ r : ℝ, 0 < r → ∀ h : ℝ → ℝ,
      IsCTSolution (ctKernel u v {0} γ) r h → ∀ s ∈ Set.Ioo 0 r,
        DifferentiableAt ℝ h s ∧ DifferentiableAt ℝ (deriv h) s ∧
        deriv (deriv h) s + h s = 6 * h s / s ^ 2) ∧
    (∀ s : ℝ, 0 < s → deriv (deriv riccatiU2) s + riccatiU2 s = 6 * riccatiU2 s / s ^ 2) ∧
    Tendsto riccatiU2 (𝓝[>] 0) (𝓝 0) ∧ (∃ s : ℝ, 0 < s ∧ riccatiU2 s ≠ 0) ∧
    (∀ r : ℝ, 0 < r → ∀ h : ℝ → ℝ,
      (∀ s ∈ Set.Ioo 0 r, DifferentiableAt ℝ h s ∧ DifferentiableAt ℝ (deriv h) s ∧
        deriv (deriv h) s + h s = 6 * h s / s ^ 2) →
      Tendsto h (𝓝[>] 0) (𝓝 0) → ∃ c : ℝ, ∀ s ∈ Set.Ioo 0 r, h s = c * riccatiU2 s) := by sorry

end Arxivmath_ph_0108008
