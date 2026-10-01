-- Prove2me | Theorems.Thm_CoulombGauss_gauss_law_from_coulomb
-- name    : CoulombGauss.gauss_law_from_coulomb
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T20:09:23.910721+00:00
-- url     : https://prove2.me/theorems/8776f383-111f-4801-b897-0808985aa5b3
-- title:
--   Gauss's law from Coulomb's law: $\lim_{R\to0^+}\Phi(R)/|B_R(r_0)|=\rho(r_0)/\varepsilon_0$
-- statement:
--   Let $\varepsilon_0>0$ be the electric constant, let $\Omega\subseteq\mathbb R^3$ be a bounded open set, and let $\rho$ be a continuous charge density on $\Omega$, integrable on $\Omega$. Let
--   $$
--   \mathbf E_0(r)=\frac{1}{4\pi\varepsilon_0}\int_\Omega\rho(r')\,\frac{r-r'}{|r-r'|^3}\,d^3r'
--   $$
--   be the electric field given by Coulomb's law and the superposition principle, and for $r_0\in\Omega$ let $\Phi(R)=\oint_{\partial B_R(r_0)}\mathbf E_0\cdot d\mathbf S$ be its outward flux through the sphere of radius $R$ about $r_0$. Then for every $r_0\in\Omega$,
--   $$
--   \lim_{R\to0^+}\frac{\Phi(R)}{|B_R(r_0)|}=\frac{\rho(r_0)}{\varepsilon_0}.
--   $$
--
--   The left-hand side is the flux-per-volume (coordinate-free) definition of $\nabla\cdot\mathbf E_0(r_0)$, so the statement is the differential form of Gauss's law, $\nabla\cdot\mathbf E_0=\rho/\varepsilon_0$, derived from Coulomb's law without the Dirac delta.
--
--   **Formalization Note** The source writes the conclusion as $\nabla\cdot\mathbf E_0(\mathbf r_0)=\lim_{R\to0}\frac1{|B_R(\mathbf r_0)|}\Phi(R)=\frac1{\varepsilon_0}\rho(\mathbf r_0)$; the formal goal asserts the limit identity (the part the proof establishes), without asserting classical differentiability of $\mathbf E_0$, which can fail for a merely continuous $\rho$. Integrability of $\rho$ on $\Omega$ is the standing assumption under which $\mathbf E_0$ is defined (it does not follow from continuity on a bounded open set). Fluxes are computed with the standard surface measure on spheres.
-- source:
--   Wikipedia, "Coulomb's law", https://en.wikipedia.org/wiki/Coulomb%27s_law (snapshot supplied as PDF, 30 Sep 2026), section "Relation to Gauss's law" -> "Deriving Gauss's law from Coulomb's law", box "Proof (without Dirac Delta)" (PDF pp. 8-9).

import Mathlib
import Definitions.Def_CoulombGauss_basic
open MeasureTheory Filter Topology Metric

namespace CoulombGauss
theorem gauss_law_from_coulomb (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (Ω : Set Vec3) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (ρ : Vec3 → ℝ) (hρc : ContinuousOn ρ Ω) (hρi : IntegrableOn ρ Ω)
    (r₀ : Vec3) (hr₀ : r₀ ∈ Ω) :
    Tendsto (fun R : ℝ => sphereFlux (electricField ε₀ ρ Ω) r₀ R / (volume (ball r₀ R)).toReal)
      (𝓝[>] 0) (𝓝 (ρ r₀ / ε₀)) := by sorry
end CoulombGauss
