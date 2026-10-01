-- Prove2me | Theorems.Thm_CoulombGauss_sphereFlux_electricField_eq_enclosed_charge
-- name    : CoulombGauss.sphereFlux_electricField_eq_enclosed_charge
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T19:04:33.444826+00:00
-- url     : https://prove2.me/theorems/fec4e750-ad68-43ca-9522-5873d53b06f5
-- title:
--   Gauss's law on small spheres: $\Phi(R)=Q(R)/\varepsilon_0$
-- statement:
--   Let $\varepsilon_0>0$, let $\Omega\subseteq\mathbb R^3$ be open, and let $\rho:\Omega\to\mathbb R$ be continuous and integrable on $\Omega$. Let
--   $$
--   \mathbf E_0(r)=\frac{1}{4\pi\varepsilon_0}\int_\Omega\rho(r')\,\frac{r-r'}{|r-r'|^3}\,d^3r' .
--   $$
--   For every $r_0\in\mathbb R^3$ and $R>0$ with $\overline B_R(r_0)\subseteq\Omega$, the flux of $\mathbf E_0$ through $\partial B_R(r_0)$ is
--   $$
--   \Phi(R)=\oint_{\partial B_R(r_0)}\mathbf E_0\cdot d\mathbf S=\frac{1}{\varepsilon_0}\int_{B_R(r_0)}\rho(r')\,d^3r' .
--   $$
--
--   This combines the source's splitting $\mathbf E_0=\mathbf E_{B_R}+\mathbf E_C$ with the two preceding flux computations.
--
--   **Formalization Note** The source takes $B_R(\mathbf r_0)\subseteq\Omega$; the formal statement asks for the closed ball to lie in $\Omega$, so that $\rho$ is continuous (hence bounded) near the sphere. Since only small $R$ matter for the goal, this loses nothing. Integrability of $\rho$ on $\Omega$ is the standing assumption under which $\mathbf E_0$ is defined.
-- source:
--   Wikipedia, "Coulomb's law", https://en.wikipedia.org/wiki/Coulomb%27s_law (snapshot supplied as PDF, 30 Sep 2026), section "Relation to Gauss's law" -> "Deriving Gauss's law from Coulomb's law", box "Proof (without Dirac Delta)" (PDF pp. 8-9).

import Mathlib
import Definitions.Def_CoulombGauss_basic
open MeasureTheory Filter Topology Metric

namespace CoulombGauss
theorem sphereFlux_electricField_eq_enclosed_charge (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (Ω : Set Vec3) (hΩ : IsOpen Ω) (ρ : Vec3 → ℝ) (hρc : ContinuousOn ρ Ω)
    (hρi : IntegrableOn ρ Ω) (r₀ : Vec3) (R : ℝ) (hR : 0 < R) (hball : closedBall r₀ R ⊆ Ω) :
    sphereFlux (electricField ε₀ ρ Ω) r₀ R = (1 / ε₀) * ∫ x in ball r₀ R, ρ x := by sorry
end CoulombGauss
