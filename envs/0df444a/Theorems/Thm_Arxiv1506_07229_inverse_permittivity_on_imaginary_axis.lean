-- Prove2me | Theorems.Thm_Arxiv1506_07229_inverse_permittivity_on_imaginary_axis
-- name    : Arxiv1506_07229.inverse_permittivity_on_imaginary_axis
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:03:29.911941+00:00
-- url     : https://prove2.me/theorems/84eccfb3-6f0d-46f2-8306-05062db1ac7c
-- title:
--   Eqs. (7)-(9): the inverse permittivity on the imaginary frequency axis
-- statement:
--   Let $f(\omega)=1/\varepsilon(q,\omega)$ at a fixed wave vector. Assume:
--
--   1. $f$ is holomorphic in $\operatorname{Im}\omega>0$ and continuous on $\operatorname{Im}\omega\ge0$;
--   2. $f(\omega)\to1$ as $|\omega|\to\infty$ with $\operatorname{Im}\omega\ge0$;
--   3. $f-1$ is integrable on the real axis;
--   4. $f(-\omega)=\overline{f(\omega)}$ for real $\omega$, so $\operatorname{Re}f$ is even and $\operatorname{Im}f$ is odd.
--
--   Then for every $u>0$:
--
--   $$\frac{1}{\varepsilon(q,iu)}-1=\frac{1}{2\pi i}\int_{-\infty}^{\infty}\frac{\frac{1}{\varepsilon(q,\omega')}-1}{\omega'-iu}\,d\omega'\qquad(7)$$
--
--   $$\frac{1}{\varepsilon(q,iu)}=1+\frac1\pi\int_0^\infty u\,\frac{\operatorname{Re}\frac{1}{\varepsilon(q,\omega')}-1}{\omega'^2+u^2}\,d\omega'+\frac1\pi\int_0^\infty\omega'\,\frac{\operatorname{Im}\frac{1}{\varepsilon(q,\omega')}}{\omega'^2+u^2}\,d\omega'\qquad(8)$$
--
--   the two integrals in (8) are equal, and
--
--   $$\frac{1}{\varepsilon(q,iu)}=1+\frac2\pi\int_0^\infty\omega'\,\frac{\operatorname{Im}\frac{1}{\varepsilon(q,\omega')}}{\omega'^2+u^2}\,d\omega'.\qquad(9)$$
--
--   The paper uses Eq. (9) to compute $1/\varepsilon$ on the imaginary axis from its values on the real axis.
--
--   **Formalization Note** The paper requires $1/\varepsilon-1$ to be analytic in the upper half-plane and to vanish at infinity, and uses the KK relations for $1/\varepsilon$. Hypotheses 1-3 make this precise: continuity up to the real axis, uniform convergence to $1$ at infinity and integrability on the real line. The KK relations for $1/\varepsilon$ are not assumed: the paper uses them only to see that the two integrals in (8) are equal, and that equality follows here from Cauchy's theorem applied at the lower-half-plane point $-iu$ together with Hypothesis 4. Hypothesis 4 is the parity used for Eq. (8).
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c006; main text, Eq. (7), unlabeled Eq. (8), Eq. (9), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem inverse_permittivity_on_imaginary_axis (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f upperHalf) (hcont : ContinuousOn f closedUpperHalf)
    (hlim : Tendsto f (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (𝓝 1))
    (hint : Integrable (fun x : ℝ => f (x : ℂ) - 1))
    (hpar : ∀ x : ℝ, f (-(x : ℂ)) = conj (f (x : ℂ)))
    (u : ℝ) (hu : 0 < u) :
    f ((u : ℂ) * Complex.I) - 1 =
        1 / (2 * π * Complex.I) * ∫ x : ℝ, (f (x : ℂ) - 1) / ((x : ℂ) - (u : ℂ) * Complex.I) ∧
      f ((u : ℂ) * Complex.I) =
        1 + (1 / π : ℝ) * ((∫ x in Set.Ioi (0 : ℝ), u * ((f (x : ℂ)).re - 1) / (x ^ 2 + u ^ 2) : ℝ) : ℂ) +
          (1 / π : ℝ) * ((∫ x in Set.Ioi (0 : ℝ), x * (f (x : ℂ)).im / (x ^ 2 + u ^ 2) : ℝ) : ℂ) ∧
      (∫ x in Set.Ioi (0 : ℝ), u * ((f (x : ℂ)).re - 1) / (x ^ 2 + u ^ 2)) =
        ∫ x in Set.Ioi (0 : ℝ), x * (f (x : ℂ)).im / (x ^ 2 + u ^ 2) ∧
      f ((u : ℂ) * Complex.I) =
        1 + (2 / π : ℝ) * ((∫ x in Set.Ioi (0 : ℝ), x * (f (x : ℂ)).im / (x ^ 2 + u ^ 2) : ℝ) : ℂ) := by sorry

end Arxiv1506_07229
