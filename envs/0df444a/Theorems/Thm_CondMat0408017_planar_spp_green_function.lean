-- Prove2me | Theorems.Thm_CondMat0408017_planar_spp_green_function
-- name    : CondMat0408017.planar_spp_green_function
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:21:43.345869+00:00
-- url     : https://prove2.me/theorems/e97ce00f-09eb-55ef-b681-49b96211e3bd
-- title:
--   Eq. (92): the planar-surface Green's function $G^{(0)}_\nu$
-- statement:
--   Let $\varepsilon,\alpha,\alpha_0$ be complex with $\alpha_0\ne0$, the values at $k$ of the dielectric function and of $\alpha(k),\alpha_0(k)$. Then (eq. 92):
--
--   1. If $\varepsilon\alpha_0+\alpha\ne0$, then $2i\alpha_0G+R^{(0)}_p=-1$ if and only if $G=\dfrac{i\varepsilon}{\varepsilon\alpha_0+\alpha}$.
--   2. If $\alpha_0+\alpha\ne0$, then $2i\alpha_0G+R^{(0)}_s=-1$ if and only if $G=\dfrac{i}{\alpha_0+\alpha}$.
--
--   So the defining relation (92a) gives the planar-surface SPP Green's functions $G^{(0)}_p(k)=i\varepsilon/(\varepsilon\alpha_0(k)+\alpha(k))$ and $G^{(0)}_s(k)=i/(\alpha_0(k)+\alpha(k))$.
--
--   **Formalization Note** $R^{(0)}_\nu$ are the Fresnel coefficients with vacuum above ($\varepsilon_0=1$).
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c015; Sec. III.G.1, eq. (Theory:def-greens-func) [(92)] with eq. (86b), PDF p. 29

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem planar_spp_green_function (eps a a0 : ℂ) (ha0 : a0 ≠ 0) :
    (eps * a0 + a ≠ 0 → ∀ G : ℂ,
      (2 * I * a0 * G + fresnelP eps a a0 = -1 ↔ G = I * eps / (eps * a0 + a))) ∧
    (a0 + a ≠ 0 → ∀ G : ℂ, (2 * I * a0 * G + fresnelS a a0 = -1 ↔ G = I / (a0 + a))) := by sorry

end CondMat0408017
