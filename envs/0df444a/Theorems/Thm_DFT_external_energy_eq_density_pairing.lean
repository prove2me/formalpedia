-- Prove2me | Theorems.Thm_DFT_external_energy_eq_density_pairing
-- name    : DFT.external_energy_eq_density_pairing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:08:46.601042+00:00
-- url     : https://prove2.me/theorems/d83cc381-8529-4b6c-a187-06ac2d650dd3
-- title:
--   The external-potential energy is a functional of the density
-- statement:
--   This is the identity from the source's "Derivation and formalism" section stating that "the
--   contribution of the external potential can be written explicitly in terms of the density".
--
--   Let $N = n+1$ electrons move in $\mathbb R^3$, let $v$ be an external potential and $\Psi$ a
--   wavefunction on configuration space $(\mathbb R^3)^N$, and let
--
--   $$\rho_\Psi(r) \;=\; \sum_{i=1}^{N}\int_{(\mathbb R^3)^{N-1}}
--      |\Psi(y_1,\dots,r,\dots,y_{N-1})|^2\,dy$$
--
--   be its one-particle density. Then the expectation value of the external potential is the
--   pairing of $v$ with the density:
--
--   $$\int_{(\mathbb R^3)^N} \Bigl(\sum_{i=1}^N v(r_i)\Bigr) |\Psi(r_1,\dots,r_N)|^2\, dr
--      \;=\; \int_{\mathbb R^3} v(r)\,\rho_\Psi(r)\,dr .$$
--
--   This identity is the structural fact on which the whole Hohenberg-Kohn framework rests: it is
--   what makes the external energy a functional of the density alone, and hence what licenses the
--   abstract model used by the other statements of this mission.
--
--   **Formalization Note.** Integrability is assumed coordinatewise, for each of the $N$ terms
--   $r \mapsto v(r_i)|\Psi|^2$ separately, since integrability of a finite sum does not follow from
--   integrability of the whole.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem external_energy_eq_density_pairing {n : ℕ} (v : Pos → ℝ) (Ψ : Config n → ℂ)
    (hv : Measurable v) (hΨ : Measurable Ψ)
    (hint : ∀ i : Fin (n + 1), Integrable fun x : Config n => v (x i) * ‖Ψ x‖ ^ 2) :
    ∫ x : Config n, (∑ i, v (x i)) * ‖Ψ x‖ ^ 2 = ∫ r : Pos, v r * oneParticleDensity Ψ r := by
  sorry

end DFT
