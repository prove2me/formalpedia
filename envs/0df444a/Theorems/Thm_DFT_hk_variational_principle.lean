-- Prove2me | Theorems.Thm_DFT_hk_variational_principle
-- name    : DFT.hk_variational_principle
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:04:52.711055+00:00
-- url     : https://prove2.me/theorems/5e20443d-6e93-4535-831f-ee27cfd2b6e0
-- title:
--   Hohenberg-Kohn Theorem 2 (variational principle)
-- statement:
--   This is Hohenberg-Kohn Theorem 2: "the functional that delivers the ground-state energy of
--   the system gives the lowest energy if and only if the input density is the true ground-state
--   density".
--
--   Fix an external potential $v$ with nondegenerate ground state $\Psi_0$, and write
--   $E_0 = E_v(\Psi_0)$ for the ground-state energy and $\rho_0 = \rho_{\Psi_0}$ for the
--   ground-state density. For every $v$-representable density $\rho$, the energy functional
--
--   $$E_v[\rho] \;=\; F[\rho] + \int v\,\rho$$
--
--   satisfies
--
--   $$E_0 \;\le\; E_v[\rho], \qquad\text{and}\qquad E_v[\rho] = E_0 \iff \rho = \rho_0 .$$
--
--   So the exact energy functional attains its minimum precisely at the ground-state density, and
--   the minimum value is the ground-state energy. This is the variational principle that every
--   practical DFT calculation minimizes.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem hk_variational_principle (M : HKModel) {v : M.Pot} {Ψ₀ : M.Wf}
    (h₀ : M.IsNondegenerateGroundState v Ψ₀) {n : M.Dens} (hn : M.VRepresentable n) :
    M.energy v Ψ₀ ≤ M.hkFunctional n + M.ext v n ∧
      (M.hkFunctional n + M.ext v n = M.energy v Ψ₀ ↔ n = M.dens Ψ₀) := by sorry

end DFT
