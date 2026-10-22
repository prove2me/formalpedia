-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_regularization_subcritical
-- name    : BirkhoffGlobalSection.eh_left_regularization_subcritical
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T14:58:11.791257+00:00
-- url     : https://prove2.me/theorems/1de51ec9-eb26-49a5-9c06-dc4e6422ecee
-- title:
--   Elliptic-hyperbolic regularization model at every subcritical parameter
-- statement:
--   For every $0<\mu<1$ and every Jacobi energy $c$ below the first critical value ($-c<h_1(\mu)$), there is a regularization model $M$ of the selected Levi-Civita component whose model Hamiltonian is the centered-left elliptic-hyperbolic Hamiltonian `ehLeftHamiltonian μ c`, and which maps the Levi-Civita component onto the selected EH component:
--
--   $$M.\mathrm{modelHamiltonian}=G_{\mu,c},\qquad M(\Sigma^{\mathrm{LC}}_{\mu,c})=\Sigma^{\mathrm{EH}}_{\mu,c}.$$
--
--   This is `eh_left_regularization_local_subcritical` without the energy window around a reference $c_0$. The explicit map $\xi=2\operatorname{arsinh}(-i\sqrt2 z)$, $y=\sqrt2\,\overline{\sqrt{1-2z^2}}\,(-iw+(\tfrac12-\mu)\bar z)$ from that proof works at every subcritical parameter. The window-free form is what a uniform-in-energy argument needs.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS2 (elliptic-hyperbolic regularization); explicit transport to the Levi-Civita model constructed in the proof of eh_left_regularization_local_subcritical (bb80df19), stated here without the energy window.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- The centered-left elliptic-hyperbolic regularization model exists at every
subcritical mass ratio and energy, with no window around a reference energy. -/
theorem eh_left_regularization_subcritical (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ M : RegularizationModel μ c,
      M.modelHamiltonian = ehLeftHamiltonian μ c ∧
      M.toModel '' leftEnergyComponent μ c = ehLeftEnergyComponent μ c := by sorry

end BirkhoffGlobalSection
