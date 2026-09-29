-- Prove2me | Theorems.Thm_DFT_hohenberg_kohn
-- name    : DFT.hohenberg_kohn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:23:57.971482+00:00
-- url     : https://prove2.me/theorems/d3218b82-b83a-4e5f-af3c-717cfc9de2f9
-- title:
--   The Hohenberg-Kohn theorems
-- statement:
--   This is the goal of the mission: the two Hohenberg-Kohn theorems, stated together.
--
--   **Part 1 (Theorem 1 and its Corollary 1).** Every ground-state property is a functional of the
--   ground-state density. For each observable $O$ defined on wavefunctions there is a functional
--   $\mathcal O$ defined on densities such that, for every external potential $v$ and every
--   nondegenerate ground state $\Psi$ of $v$,
--
--   $$O(\Psi) \;=\; \mathcal O(\rho_\Psi).$$
--
--   The functional $\mathcal O$ depends only on $O$, not on the potential: one and the same
--   density functional returns the value of that observable for every system.
--
--   **Part 2 (Theorem 2).** For every potential $v$ with nondegenerate ground state $\Psi_0$, and
--   every $v$-representable density $\rho$,
--
--   $$E_v[\rho_0] \;\le\; E_v[\rho], \qquad E_v[\rho] = E_v[\rho_0] \iff \rho = \rho_0,$$
--
--   where $E_v[\rho] = F[\rho] + \int v \rho$ and $\rho_0 = \rho_{\Psi_0}$ is the ground-state
--   density. The exact energy functional attains its minimum exactly at the true ground-state
--   density, and the minimal value is the ground-state energy.
--
--   Together these are the two statements that make the electron density, rather than the
--   $3N$-dimensional wavefunction, a legitimate basic variable of quantum many-body theory.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem hohenberg_kohn (M : HKModel) :
    (∀ O : M.Wf → ℝ, ∃ O' : M.Dens → ℝ, ∀ (v : M.Pot) (Ψ : M.Wf),
        M.IsNondegenerateGroundState v Ψ → O Ψ = O' (M.dens Ψ)) ∧
      (∀ (v : M.Pot) (Ψ₀ : M.Wf), M.IsNondegenerateGroundState v Ψ₀ →
        ∀ n : M.Dens, M.VRepresentable n →
          M.hkFunctional (M.dens Ψ₀) + M.ext v (M.dens Ψ₀) ≤ M.hkFunctional n + M.ext v n ∧
            (M.hkFunctional n + M.ext v n
                = M.hkFunctional (M.dens Ψ₀) + M.ext v (M.dens Ψ₀) ↔ n = M.dens Ψ₀)) := by
  sorry

end DFT
