-- Prove2me | Theorems.Thm_Arxiv1506_07229_inverse_permittivity_zero_on_imaginary_axis
-- name    : Arxiv1506_07229.inverse_permittivity_zero_on_imaginary_axis
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:03:00.753181+00:00
-- url     : https://prove2.me/theorems/b3aa385f-0d71-450b-a366-5da005167abc
-- title:
--   Eq. (6): $1/\varepsilon$ has a zero on the positive imaginary axis, a pole of $\varepsilon$
-- statement:
--   Let $f(\omega)=1/\varepsilon(q,\omega)$ be the inverse permittivity at a fixed wave vector, defined on $\mathbb{C}$. Assume:
--
--   1. $f$ is holomorphic in the upper half-plane $\operatorname{Im}\omega>0$ (causality of $1/\varepsilon$);
--   2. (a) $u\mapsto f(iu)$ is real-valued and continuous on $u\ge0$;
--   3. (b) $f(0)<0$;
--   4. (c) $f(iu)\to1$ as $u\to+\infty$.
--
--   Then there is $u_s>0$ such that $\omega_s=iu_s$ satisfies
--
--   $$\frac{1}{\varepsilon(q,\omega_s)}=f(iu_s)=0\qquad\text{(Eq. (6))},$$
--
--   and $\varepsilon=1/f$ has a pole at $\omega_s$: $|1/f(\omega)|\to\infty$ as $\omega\to\omega_s$, $\omega\ne\omega_s$.
--
--   This is the paper's explanation of the failure of the KK relations for $\varepsilon$ when $q>q_c$. The permittivity acquires a pole in the upper half-plane, on the imaginary axis.
--
--   **Formalization Note** Holomorphy of $f$ in the upper half-plane is used by the paper but not listed among (a)-(c). It is needed for the statement that the singularity of $\varepsilon$ is a pole. Condition (a) includes the point $u=0$, as continuity there is needed to combine (a) with (b). The theorem is stated for one fixed wave vector, abstracting from the numerical input $q>q_c$ behind (b).
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c005; main text after Eq. (5), Eq. (6) and conditions (a)-(c), PDF p. 2-3

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem inverse_permittivity_zero_on_imaginary_axis (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f upperHalf)
    (ha_real : ∀ u : ℝ, 0 ≤ u → (f ((u : ℂ) * Complex.I)).im = 0)
    (ha_cont : ContinuousOn (fun u : ℝ => f ((u : ℂ) * Complex.I)) (Set.Ici 0))
    (hb : (f 0).re < 0)
    (hc : Tendsto (fun u : ℝ => f ((u : ℂ) * Complex.I)) atTop (𝓝 1)) :
    ∃ u : ℝ, 0 < u ∧ f ((u : ℂ) * Complex.I) = 0 ∧
      Tendsto (fun z => ‖(f z)⁻¹‖) (𝓝[≠] ((u : ℂ) * Complex.I)) atTop := by sorry

end Arxiv1506_07229
