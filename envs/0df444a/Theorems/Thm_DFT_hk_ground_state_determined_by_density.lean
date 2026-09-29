-- Prove2me | Theorems.Thm_DFT_hk_ground_state_determined_by_density
-- name    : DFT.hk_ground_state_determined_by_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T19:58:06.922041+00:00
-- url     : https://prove2.me/theorems/37b72df5-3b4f-4848-bb66-8bd7d25f11e2
-- title:
--   Hohenberg-Kohn Theorem 1 (the density determines the state)
-- statement:
--   This is the wavefunction half of Hohenberg-Kohn Theorem 1, in the form "the ground-state
--   density determines the many-body wavefunction".
--
--   Let $\Psi_1$ be a nondegenerate ground state of the external potential $v_1$ and $\Psi_2$ a
--   nondegenerate ground state of the external potential $v_2$, in the same Hohenberg-Kohn model
--   (same admissible states, same universal functional $F$, same density map). If the two states
--   have the same one-particle density,
--
--   $$\rho_{\Psi_1} \;=\; \rho_{\Psi_2},$$
--
--   then $\Psi_1 = \Psi_2$.
--
--   The two potentials are unrelated: they need not differ by a constant, and no relation
--   between the corresponding ground-state energies is assumed. Nondegeneracy is essential and is
--   the hypothesis under which the original Hohenberg-Kohn argument is stated; for degenerate
--   ground states the conclusion fails as stated, since several distinct minimizers can share a
--   density.
--
--   This statement is the source of the whole "everything is a functional of the density"
--   program: once the state is pinned down by the density, so is every ground-state expectation
--   value.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem hk_ground_state_determined_by_density (M : HKModel) {v₁ v₂ : M.Pot} {Ψ₁ Ψ₂ : M.Wf}
    (h₁ : M.IsNondegenerateGroundState v₁ Ψ₁) (h₂ : M.IsNondegenerateGroundState v₂ Ψ₂)
    (hd : M.dens Ψ₁ = M.dens Ψ₂) : Ψ₁ = Ψ₂ := by sorry

end DFT
