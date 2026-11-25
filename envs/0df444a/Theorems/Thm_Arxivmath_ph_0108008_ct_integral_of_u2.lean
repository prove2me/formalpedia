-- Prove2me | Theorems.Thm_Arxivmath_ph_0108008_ct_integral_of_u2
-- name    : Arxivmath_ph_0108008.ct_integral_of_u2
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:37:10.948639+00:00
-- url     : https://prove2.me/theorems/ee54eddc-61eb-41ac-9b76-9e94ac9a44e0
-- title:
--   Section 2, proof of the Claim: $J=u_2(s)+p(r)u_0(s)$
-- statement:
--   Let $u_m,v_m$ be families with $u_0=\sin$, $v_0=-\cos$. Take $S=\{0\}$, $T=\{2\}$ and $\gamma$ satisfying (1.2), so that $\gamma_0=-6$. Let $g$ be the corresponding kernel and $g_0(s,t)=-\sin(\min(s,t))\cos(\max(s,t))$. Then for every $r>0$ and $s\in[0,r]$,
--   $$-\int_0^r g(s,t)u_2(t)t^{-2}\,dt=\int_0^r g_0(s,t)\,6u_2(t)t^{-2}\,dt=\int_0^r g_0(s,t)\,(u_2''+u_2)(t)\,dt=u_2(s)+p(r)\,u_0(s).$$
--   Consequently, if $p(r)=0$ for some $r>0$, then $h=u_2$ solves (1.1) on $[0,r]$, in the sense of the definitions.
--
--   **Formalization Note** The paper takes $0<s<r$. The identity also holds at $s=0$ and $s=r$, and is stated on $[0,r]$, because a solution of (1.1) is defined on $[0,r]$.
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1, claim c006; Section 2, Proof of the Claim, displayed equations for J, PDF p. 2

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

namespace Arxivmath_ph_0108008

theorem ct_integral_of_u2 (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) (γ : ℝ → ℝ) (hγ : CTCoeffEq {0} {2} γ) :
    (∀ r : ℝ, 0 < r → ∀ s ∈ Set.Icc 0 r,
      -(∫ t in (0 : ℝ)..r, ctKernel u v {0} γ s t * riccatiU2 t * (t ^ 2)⁻¹) =
          ∫ t in (0 : ℝ)..r, greenG0 s t * (6 * riccatiU2 t * (t ^ 2)⁻¹) ∧
      (∫ t in (0 : ℝ)..r, greenG0 s t * (6 * riccatiU2 t * (t ^ 2)⁻¹)) =
          ∫ t in (0 : ℝ)..r, greenG0 s t * (deriv (deriv riccatiU2) t + riccatiU2 t) ∧
      (∫ t in (0 : ℝ)..r, greenG0 s t * (deriv (deriv riccatiU2) t + riccatiU2 t)) =
          riccatiU2 s + wronskP r * Real.sin s) ∧
    (∀ r : ℝ, 0 < r → wronskP r = 0 → IsCTSolution (ctKernel u v {0} γ) r riccatiU2) := by sorry

end Arxivmath_ph_0108008
