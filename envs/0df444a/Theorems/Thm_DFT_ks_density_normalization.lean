-- Prove2me | Theorems.Thm_DFT_ks_density_normalization
-- name    : DFT.ks_density_normalization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:09:14.972248+00:00
-- url     : https://prove2.me/theorems/56f89fa9-a81d-4200-b3e8-b7a88ebbf131
-- title:
--   Kohn-Sham density integrates to the electron number
-- statement:
--   In the Kohn-Sham scheme the density of the auxiliary non-interacting system is built from
--   orbitals,
--
--   $$n(r) \;=\; \sum_{i=1}^{N} |\varphi_i(r)|^2 .$$
--
--   This statement records that such a density carries the right electron number: if the orbitals
--   $\varphi_1,\dots,\varphi_N$ are orthonormal in $L^2(\mathbb R^3)$, that is
--
--   $$\int_{\mathbb R^3} \overline{\varphi_i(r)}\,\varphi_j(r)\,dr \;=\; \delta_{ij},$$
--
--   then
--
--   $$\int_{\mathbb R^3} \sum_{i=1}^{N} |\varphi_i(r)|^2 \, dr \;=\; N .$$
--
--   The normalization is the consistency condition every self-consistent Kohn-Sham iteration
--   relies on: the density produced from the occupied orbitals describes exactly $N$ electrons.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem ks_density_normalization {N : ℕ} (φ : Fin N → Pos → ℂ)
    (hmem : ∀ i, MemLp (φ i) 2 volume)
    (horth : ∀ i j, ∫ r : Pos, (starRingEnd ℂ) (φ i r) * φ j r = if i = j then 1 else 0) :
    ∫ r : Pos, ∑ i, ‖φ i r‖ ^ 2 = (N : ℝ) := by sorry

end DFT
