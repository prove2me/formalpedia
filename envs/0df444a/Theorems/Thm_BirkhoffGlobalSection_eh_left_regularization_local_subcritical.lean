-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_regularization_local_subcritical
-- name    : BirkhoffGlobalSection.eh_left_regularization_local_subcritical
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T01:06:28.990985+00:00
-- url     : https://prove2.me/theorems/bb80df19-72d8-4442-a21c-427a341230c9
-- title:
--   Collision-compatible Levi-Civita to elliptic-hyperbolic coordinates near a fixed subcritical energy
-- statement:
--   Fix $c_0>2$. For some $\varepsilon,\eta>0$, whenever
--
--   $$0<\mu<1,\qquad |\mu-1/2|<\varepsilon,\qquad |c-c_0|<\eta,\qquad -c<h_1(\mu),$$
--
--   the selected Levi-Civita component admits a smooth regularization model $R$ satisfying
--
--   $$R.\mathrm{modelHamiltonian}=G_{\mu,c},\qquad R.\mathrm{toModel}(\Sigma^{\mathrm{LC}}_{\mu,c})=\Sigma^{\mathrm{EH}}_{\mu,c}.$$
--
--   Here $G$ is the explicit elliptic-hyperbolic Hamiltonian centered at the left primary, and $\Sigma^{\mathrm{EH}}$ is its zero-level component through the designated collision point. The model includes mutually inverse smooth coordinate maps on open neighborhoods, a positive constant conformal symplectic factor, antipodal equivariance on the component, a regular model level, and a continuous positive factor relating the two Hamiltonian vector fields, including at collisions.
--
--   This separates the coordinate-identification obligation from convexity of the explicit elliptic-hyperbolic surface. No convexity or global surface of section is asserted.
--
--   **Formalization Note.** This is a new transport lemma adapting the coordinate formulas in Section 9.2 to the platform's Levi-Civita normalization. Its collision extension and component identification are substantive parts of the assertion; they are not claimed to follow solely from the paper's off-collision double covering.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS2, Section 9.2, centered Jacobi Hamiltonian, symplectic elliptic-coordinate transformation, and regularized Hamiltonian formulas; Section 4, regularized dynamics. New local transport lemma for the Prove2Me Levi-Civita normalization, with collision extension explicitly included.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.eh_left_regularization_local_subcritical
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∃ M : RegularizationModel μ c,
          M.modelHamiltonian = ehLeftHamiltonian μ c ∧
          M.toModel '' leftEnergyComponent μ c = ehLeftEnergyComponent μ c := by sorry
