-- Prove2me | Theorems.Thm_DFT_levy_constrained_search
-- name    : DFT.levy_constrained_search
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:05:44.213979+00:00
-- url     : https://prove2.me/theorems/1d4fe418-8178-4345-8a56-2ade69efac04
-- title:
--   Levy constrained-search identity
-- statement:
--   This is Levy's constrained-search formulation of the variational principle, cited in the
--   source material as the resolution of the $v$-representability problem.
--
--   Define the constrained-search functional on densities by minimizing the universal energy over
--   all wavefunctions with a prescribed density,
--
--   $$F_{\mathrm{LL}}[\rho] \;=\; \inf\{ F(\Psi) \;:\; \rho_\Psi = \rho \}.$$
--
--   If $\Psi_0$ is a ground state of the external potential $v$ — here ordinary, not necessarily
--   nondegenerate — then the ground-state energy is recovered by a two-stage minimization, first
--   over states with a given density and then over densities:
--
--   $$E_v(\Psi_0) \;=\; \inf_{\rho} \Bigl( F_{\mathrm{LL}}[\rho] + \int v \rho \Bigr),$$
--
--   where the outer infimum ranges over densities that actually arise as the density of some
--   admissible state.
--
--   Unlike the Hohenberg-Kohn functional, $F_{\mathrm{LL}}$ is defined on every such density
--   without any $v$-representability requirement, which is exactly why Levy's formulation is the
--   standard foundation for the modern treatment.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem levy_constrained_search (M : HKModel) {v : M.Pot} {Ψ₀ : M.Wf}
    (h : M.IsGroundState v Ψ₀) :
    M.energy v Ψ₀ = sInf ((fun n => M.levyFunctional n + M.ext v n) '' Set.range M.dens) := by
  sorry

end DFT
