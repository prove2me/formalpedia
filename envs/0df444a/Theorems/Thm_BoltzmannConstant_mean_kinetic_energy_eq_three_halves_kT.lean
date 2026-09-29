-- Prove2me | Theorems.Thm_BoltzmannConstant_mean_kinetic_energy_eq_three_halves_kT
-- name    : BoltzmannConstant.mean_kinetic_energy_eq_three_halves_kT
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:53:20.44429+00:00
-- url     : https://prove2.me/theorems/03a87908-4ccc-4e79-9cb8-0dab628cba19
-- title:
--   Mean translational kinetic energy of an ideal gas is $\tfrac{3}{2}k_BT$
-- statement:
--   Consider $N > 0$ particles of mass $m > 0$ in a vessel of volume $V > 0$ at absolute temperature $T > 0$, exerting pressure $p$, and write $\langle v^2 \rangle$ for the mean square particle speed. Kinetic theory gives the pressure of an ideal gas as $$pV = \tfrac{1}{3} N m \langle v^2 \rangle,$$ while the per-molecule ideal gas law gives $$pV = N k_B T.$$ Combining the two identifies the characteristic energy $k_BT$ with the mechanical motion of the particles: the mean translational kinetic energy of a particle is $$\tfrac{1}{2} m \langle v^2 \rangle = \tfrac{3}{2} k_B T,$$ and consequently the root-mean-square speed is $$v_{\mathrm{rms}} = \sqrt{\langle v^2 \rangle} = \sqrt{3 k_B T / m}.$$ This is the statement that makes $k_B$ the conversion factor between temperature and microscopic energy.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Role in the equipartition of energy" (kinetic pressure formula, mean translational kinetic energy, root-mean-square speed)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem mean_kinetic_energy_eq_three_halves_kT
    (N m V p T msq : ℝ) (hN : 0 < N) (hV : 0 < V) (hm : 0 < m) (hT : 0 < T)
    (hkinetic : p * V = N * m * msq / 3)
    (hgas : p * V = N * kB * T) :
    m * msq / 2 = 3 / 2 * (kB * T) ∧ Real.sqrt msq = Real.sqrt (3 * kB * T / m) := by sorry

end BoltzmannConstant
