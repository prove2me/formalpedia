-- Prove2me | Theorems.Thm_CarneiroDeSitter_planeWave_energy_density
-- name    : CarneiroDeSitter.planeWave_energy_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T02:11:51.462742+00:00
-- url     : https://prove2.me/theorems/1ba6806f-2c27-450b-b4b9-188c4a3809f7
-- title:
--   Eqs. (9)–(10): energy density of the damped plane wave, $\rho=(\omega^2+b^2)\phi\phi^\dagger$
-- statement:
--   Let $\omega>0$, $H\in\mathbb R$, $\phi_0\in\mathbb C$, let $k=k(\omega,H)$ and $b=b(\omega,H)$ be given by Eqs. (7)–(8), and let $\phi(t,r)=\phi_0e^{-br}e^{-i(\omega t-kr)}$. The time component of the energy–momentum tensor (9), for a field depending only on $t$ and $r$ with signature $(+,-,-,-)$, is
--   $$
--   \rho=|\partial_t\phi|^2-\tfrac12\big(|\partial_t\phi|^2-|\partial_r\phi|^2\big).
--   $$
--   Then at every point $(t,r)$
--   $$
--   \rho=(\omega^2+b^2)\,|\phi(t,r)|^2 .
--   $$
--
--   This is Eq. (10); the paper reads it as a thermal motion of temperature $b$ superposed on the mode of frequency $\omega$.
--
--   **Formalization Note** $|z|^2$ is `Complex.normSq z`, i.e. $\phi\phi^\dagger$.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, p. 2243, Eqs. (9), (10)

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set

namespace CarneiroDeSitter

theorem planeWave_energy_density (ω H : ℝ) (hω : 0 < ω) (φ₀ : ℂ) (t r : ℝ) :
    let b := dampingRate ω H
    let φ := planeWave φ₀ b ω (waveNumber ω H)
    let φt := deriv (fun s => φ s r) t
    let φr := deriv (fun x => φ t x) r
    Complex.normSq φt - (1 / 2) * (Complex.normSq φt - Complex.normSq φr)
      = (ω ^ 2 + b ^ 2) * Complex.normSq (φ t r) := by sorry

end CarneiroDeSitter
