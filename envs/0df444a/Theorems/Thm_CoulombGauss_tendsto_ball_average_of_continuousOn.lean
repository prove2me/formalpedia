-- Prove2me | Theorems.Thm_CoulombGauss_tendsto_ball_average_of_continuousOn
-- name    : CoulombGauss.tendsto_ball_average_of_continuousOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T19:46:21.919659+00:00
-- url     : https://prove2.me/theorems/c40255ce-e5c8-4902-8ea5-163bcb06b30f
-- title:
--   Ball averages of a continuous density converge: $\frac{1}{|B_R|}\int_{B_R(c)}\rho\to\rho(c)$
-- statement:
--   Let $U\subseteq\mathbb R^3$ be open, let $\rho$ be continuous on $U$, and let $c\in U$. Then
--   $$
--   \lim_{R\to0^+}\frac{1}{|B_R(c)|}\int_{B_R(c)}\rho(r')\,d^3r'=\rho(c),
--   $$
--   where $|B_R(c)|$ is the Lebesgue volume of the ball.
--
--   In the source this is the final step: "$\frac1{\varepsilon_0}\int_{B_R}\rho=\frac1{\varepsilon_0}\rho(\mathbf r'_c)|B_R(\mathbf r_0)|$ with $\mathbf r'_c\in B_R(\mathbf r_0)$, by the mean value theorem for integrals; using the squeeze theorem and the continuity of $\rho$ …".
--
--   **Formalization Note** The limit is taken along $R\to0$ with $R>0$.
-- source:
--   Wikipedia, "Coulomb's law", https://en.wikipedia.org/wiki/Coulomb%27s_law (snapshot supplied as PDF, 30 Sep 2026), section "Relation to Gauss's law" -> "Deriving Gauss's law from Coulomb's law", box "Proof (without Dirac Delta)" (PDF pp. 8-9).

import Mathlib
import Definitions.Def_CoulombGauss_basic
open MeasureTheory Filter Topology Metric

namespace CoulombGauss
theorem tendsto_ball_average_of_continuousOn (U : Set Vec3) (hU : IsOpen U) (ρ : Vec3 → ℝ)
    (hρ : ContinuousOn ρ U) (c : Vec3) (hc : c ∈ U) :
    Tendsto (fun R : ℝ => (volume (ball c R)).toReal⁻¹ * ∫ x in ball c R, ρ x)
      (𝓝[>] 0) (𝓝 (ρ c)) := by sorry
end CoulombGauss
