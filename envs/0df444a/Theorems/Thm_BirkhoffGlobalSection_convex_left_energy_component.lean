-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_left_energy_component
-- name    : BirkhoffGlobalSection.convex_left_energy_component
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T18:37:22.784131+00:00
-- url     : https://prove2.me/theorems/41e5f625-b92a-4810-a5e2-13dba5a46c83
-- title:
--   Convexity of the Levi-Civita component in the validated range (Theorem 1.5)
-- statement:
--   We work in the planar circular restricted three-body problem with mass parameter $\mu$ and Jacobi energy $H=-c$, in the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ at the primary of mass $1-\mu$. Let $\Sigma_{\mu,c}\subset\mathbb R^4$ be the compact component of the regularized energy surface $\{K_{\mu,c}=0\}$ over that primary (`leftEnergyComponent`).
--
--   For
--
--   $$
--   0<\mu\le\frac12,\qquad \frac{21}{10}\le c\le\frac{21}{10}+10^{-6},
--   $$
--
--   the component $\Sigma_{\mu,c}$ bounds a convex region. Precisely, the set
--
--   $$
--   \widehat\Sigma_{\mu,c}=\{\,t\,s:\ s\in\Sigma_{\mu,c},\ 0\le t\le1\,\}
--   $$
--
--   is convex. (Since $\Sigma_{\mu,c}$ is star-shaped with respect to the origin, $\widehat\Sigma_{\mu,c}$ is exactly the compact region it encloses.)
--
--   This is the positive-mass part of the first sentence of Theorem 1.5 of Joung–van Koert ("the compact component of the Levi-Civita regularization is convex"). Convexity implies dynamical convexity (Hofer–Wysocki–Zehnder), which is the hypothesis under which Hryniewicz's criterion shows that the retrograde and direct orbits of Theorem 1.2 bind disk-like global surfaces of section (the milestone "Theorems 1.2 and 1.5 — validated ordinary global sections").
--
--   **Formalization Note.** The endpoint $\mu=0$ is omitted, as in the milestone statement `validated_range_retrograde_and_direct_global_sections`.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Theorem 1.5 (first sentence), restricted to 0 < mu <= 1/2 as in the milestone statement validated_range_retrograde_and_direct_global_sections.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

/-- Joung--van Koert, Theorem 1.5 (first sentence), positive-mass part: in the validated
parameter range the compact Levi-Civita component bounds a convex region. -/
theorem convex_left_energy_component (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000) :
    Convex ℝ {y : Phase | ∃ s ∈ leftEnergyComponent μ c, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s} := by sorry

end BirkhoffGlobalSection
