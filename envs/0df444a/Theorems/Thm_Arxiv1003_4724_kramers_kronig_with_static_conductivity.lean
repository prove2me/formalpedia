-- Prove2me | Theorems.Thm_Arxiv1003_4724_kramers_kronig_with_static_conductivity
-- name    : Arxiv1003_4724.kramers_kronig_with_static_conductivity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:59:09.658476+00:00
-- url     : https://prove2.me/theorems/a72ed968-5b64-48f5-8c30-fd927a97d995
-- title:
--   Eqs. (27)-(28) (as proved): Kramers-Kronig relations for $\varepsilon(\omega)$ with the static-conductivity pole $4\pi i\sigma_{st}/\omega$
-- statement:
--   Let $\varepsilon(z)$ be the long-wavelength permittivity, holomorphic in the upper half-plane $\operatorname{Im}z>0$, and let $\sigma_{st}$ be the static conductivity (any real number; the paper's case is $\sigma_{st}>0$). Suppose that, apart from the pole $4\pi i\sigma_{st}/z$ at $z=0$, $\varepsilon$ has no singularity on the closed upper half-plane: in particular the remainder $g$ below is continuous at $z=0$. Precisely,
--
--   $$\varepsilon(z)=1+\frac{4\pi i\sigma_{st}}{z}+g(z)\qquad(\operatorname{Im}z\ge0,\ z\ne0),$$
--
--   with $g$ continuous on $\operatorname{Im}z\ge0$ and $g(z)\to0$ as $|z|\to\infty$ there. On the real axis $\varepsilon(\omega)$ denotes the boundary value $\varepsilon(\omega+i0)$. Then for every real $\omega\ne0$
--
--   $$\operatorname{Re}\varepsilon(\omega)=1+P\!\int_{-\infty}^\infty\frac{\operatorname{Im}\varepsilon(\xi)}{\pi}\frac{d\xi}{\xi-\omega},\qquad \operatorname{Im}\varepsilon(\omega)=-P\!\int_{-\infty}^\infty\frac{\operatorname{Re}\varepsilon(\xi)-1}{\pi}\frac{d\xi}{\xi-\omega}+\frac{4\pi\sigma_{st}}{\omega},$$
--
--   where $P$ is the principal value at $\xi=\omega$ and at $\xi=0$ and the symmetric limit at infinity (eqs. 27-28).
--
--   These are the Kramers-Kronig relations for a medium with finite non-zero static conductivity. The extra term $4\pi\sigma_{st}/\omega$ accounts for the low-frequency singularity of $\varepsilon(\omega)$.
--
--   **Formalization Note** The paper presents (27)-(28) as a consequence of the positivity $\varepsilon(q\to0,0)>0$, but its derivation ("Therefore [9]") uses only the analyticity of $\varepsilon(z)$ in the upper half-plane and the pole $4\pi i\sigma_{st}/\omega$. These, together with the regularity and decay that the form "$1+P\!\int$" presupposes, are the hypotheses. Positivity is not one, which is why the title says "as proved". $\operatorname{Im}\varepsilon(\xi)\sim4\pi\sigma_{st}/\xi$ near $\xi=0$, so the principal value in (27) is also needed at $\xi=0$. In (28) the integrand is continuous at $0$, so excluding a neighbourhood of $0$ does not change the value. Boundary values are encoded by continuity of $g$ up to the real axis. Continuity of $g$ at $0$ excludes the further possibility, mentioned in the paper after (28), that $\operatorname{Re}\varepsilon(\omega)$ is itself singular as $\omega\to0$; the statement covers only the case where the pole is the sole singularity at $0$. No sign of $\sigma_{st}$ is needed: the paper's $\sigma_{st}>0$ is a special case, and $\sigma_{st}=0$ gives the ordinary Kramers-Kronig relations.
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), claim c006; Sec. II, eqs. (27)-(28), PDF p. 6; restated in Sec. IV, PDF p. 7, and in the abstract

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology

namespace Arxiv1003_4724

theorem kramers_kronig_with_static_conductivity (eps g : ℂ → ℂ) (sigmaSt : ℝ)
    (hhol : DifferentiableOn ℂ eps {w : ℂ | 0 < w.im})
    (hg : ContinuousOn g {w : ℂ | 0 ≤ w.im})
    (heps : ∀ w : ℂ, 0 ≤ w.im → w ≠ 0 →
      eps w = 1 + 4 * Real.pi * Complex.I * sigmaSt / w + g w)
    (hinf : Tendsto g (Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 ≤ w.im}) (𝓝 0)) :
    ∀ x : ℝ, x ≠ 0 →
      HasPVIntegral (fun ξ => (eps ξ).im / Real.pi / (ξ - x)) {0, x} ((eps x).re - 1) ∧
      HasPVIntegral (fun ξ => -((eps ξ).re - 1) / Real.pi / (ξ - x)) {0, x}
        ((eps x).im - 4 * Real.pi * sigmaSt / x) := by sorry

end Arxiv1003_4724
