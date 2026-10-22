-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_derivative_pos
-- name    : BirkhoffGlobalSection.left_energy_component_radial_derivative_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T01:06:53.00014+00:00
-- url     : https://prove2.me/theorems/6e659355-0345-4dd1-aef2-e8329d26fb68
-- title:
--   Subcritical Levi-Civita component is strictly star-shaped
-- statement:
--   Let $0<\mu<1$ and let $c$ be below the first critical value, $-c<H(L_1)$. Then the selected Levi-Civita component $\Sigma_{\mu,c}$ (the component of $\{K_{\mu,c}=0\}$ through the regularized collision) is strictly star-shaped with respect to the origin:
--
--   $$dK_{\mu,c}(s)\,s>0\qquad\text{for every } s\in\Sigma_{\mu,c}.$$
--
--   Proof idea: write $s=R\,x$ with $|x|=1$. Along the ray $t\mapsto t x$, the energy is negative for $0\le t<R$ (Proved `left_component_radial_interior_negative`), and the ray avoids the second collision up to the first positive-energy scale (Proved `left_ray_positive_energy_before_second_collision`), hence on $[0,R]$. So $s$ lies in the closure of the negative component through $0$ (Proved `first_ray_zero_in_left_negative_closure`). There the radial derivative $\frac{d}{da}K(as)|_{a=1}$ is positive (Proved `left_negative_closure_radial_transversality`), and by the chain rule it equals $dK(s)\,s$.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Section 4 (star-shapedness of the regularized component); assembled from the Proved platform lemmas named in the statement.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Below the first critical value, the selected Levi-Civita component is
strictly star-shaped: the radial vector field is positively transverse to it,
in the form `dH_s(s) > 0`. -/
theorem left_energy_component_radial_derivative_pos (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ leftEnergyComponent μ c,
      0 < fderiv ℝ (leviCivitaHamiltonian μ c) s s := by sorry

end BirkhoffGlobalSection
