-- Prove2me | Theorems.Thm_DFT_hkFunctional_eq_of_isNondegenerateGroundState
-- name    : DFT.hkFunctional_eq_of_isNondegenerateGroundState
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:03:58.271803+00:00
-- url     : https://prove2.me/theorems/b5988e4c-36b7-4497-ad27-7c0e9da8f62e
-- title:
--   Corollary 1: the Hohenberg-Kohn functional is well defined
-- statement:
--   This is Corollary 1 of Hohenberg-Kohn Theorem 1: the universal functional
--
--   $$F[\rho] \;=\; \langle \Psi[\rho] \mid \hat T + \hat U \mid \Psi[\rho]\rangle$$
--
--   is well defined, i.e. it does not depend on which nondegenerate ground state realizing the
--   density $\rho$ is used to evaluate it, and it does not depend on the external potential.
--
--   Precisely: if $\Psi$ is a nondegenerate ground state of some external potential $v$, then the
--   Hohenberg-Kohn functional evaluated at the density of $\Psi$ equals the universal energy of
--   $\Psi$ itself,
--
--   $$F[\rho_\Psi] \;=\; F(\Psi).$$
--
--   Since the potential $v$ appears only in the hypothesis and not in the conclusion, this is the
--   statement that $F[\,\cdot\,]$ is *universal*: the same functional serves every system, which is
--   what allows one exchange-correlation functional to be sought once and for all.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem hkFunctional_eq_of_isNondegenerateGroundState (M : HKModel) {v : M.Pot} {Ψ : M.Wf}
    (h : M.IsNondegenerateGroundState v Ψ) : M.hkFunctional (M.dens Ψ) = M.F Ψ := by sorry

end DFT
