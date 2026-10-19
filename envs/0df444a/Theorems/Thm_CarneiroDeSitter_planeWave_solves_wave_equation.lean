-- Prove2me | Theorems.Thm_CarneiroDeSitter_planeWave_solves_wave_equation
-- name    : CarneiroDeSitter.planeWave_solves_wave_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T02:09:48.480967+00:00
-- url     : https://prove2.me/theorems/9a9bce4f-fd68-4589-ba43-ec251edd888d
-- title:
--   Eqs. (5)–(8): the damped plane wave solves $\ddot\phi+3H\dot\phi-\partial_r^2\phi=0$
-- statement:
--   Let $\omega>0$, let $H\in\mathbb R$ be a constant Hubble parameter, and let $\phi_0\in\mathbb C$. Put $k=k(\omega,H)$ and $b=b(\omega,H)$ as in Eqs. (7)–(8),
--   $$
--   k=\frac{\sqrt2\,\omega}{2}\Big(1+\sqrt{1+(3H/\omega)^2}\Big)^{1/2},\qquad b=\frac{3\sqrt2\,H}{2}\Big(1+\sqrt{1+(3H/\omega)^2}\Big)^{-1/2},
--   $$
--   and $\phi(t,r)=\phi_0e^{-br}e^{-i(\omega t-kr)}$. Then at every point $(t,r)$
--   $$
--   \frac{\partial^2\phi}{\partial t^2}+3H\frac{\partial\phi}{\partial t}-\frac{\partial^2\phi}{\partial r^2}=0 .
--   $$
--
--   This is Eq. (5) for a radial plane wave with slowly varying (here: constant) $H$, and it shows that the amplitude decays with depth length $b^{-1}$.
--
--   **Formalization Note** $H$ is a constant, as in the paper's approximation that $H$ varies slowly compared with the wave; the Laplacian of the radial plane wave is taken as $\partial_r^2$. Derivatives are derivatives of complex-valued functions of one real variable.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, p. 2243, Eqs. (5), (6), (7), (8)

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set

namespace CarneiroDeSitter

theorem planeWave_solves_wave_equation (ω H : ℝ) (hω : 0 < ω) (φ₀ : ℂ) (t r : ℝ) :
    let φ := planeWave φ₀ (dampingRate ω H) ω (waveNumber ω H)
    deriv (deriv (fun s => φ s r)) t + 3 * H * deriv (fun s => φ s r) t
      - deriv (deriv (fun x => φ t x)) r = 0 := by sorry

end CarneiroDeSitter
