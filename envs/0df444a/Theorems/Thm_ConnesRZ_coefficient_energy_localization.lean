-- Prove2me | Theorems.Thm_ConnesRZ_coefficient_energy_localization
-- name    : ConnesRZ.coefficient_energy_localization
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T22:21:28.88691+00:00
-- url     : https://prove2.me/theorems/f41e2fb4-cde4-4a2b-8572-cb585fc148e0
-- title:
--   Fixed-packet Mellin interpolation with arbitrarily small complementary coefficient energy
-- statement:
--   Let $Z=\{\rho\in\mathbb C:\zeta(\rho)=0,\ 0<\operatorname{Re}\rho<1\}$, and let $m_\rho$ be the analytic multiplicity of the actual Riemann-zeta zero $\rho$. For a smooth compactly supported function $g:\mathbb R\to\mathbb C$, write
--   $$\widehat g(z)=\int_{\mathbb R}g(t)e^{(z-1/2)t}\,dt.$$
--   For any finite set $S\subset Z$, any prescribed values $a:S\to\mathbb C$, and any $\varepsilon>0$, there exists such a test function satisfying
--   $$\widehat g(\rho)=a(\rho)\quad(\rho\in S),\qquad
--   \sum_{\rho\in Z\setminus S}m_\rho\,|\widehat g(\rho)|^2<\varepsilon.$$
--   The complementary nonnegative energy family is unconditionally summable. The selected set remains fixed, every other actual zero is retained, and analytic multiplicities are preserved. No reflection closure, RH hypothesis, Weil-positivity assumption, or common support radius is required.
--
--   This strengthens the complementary signed-product control used in the [existing Weil positivity criterion](https://prove2.me/theorems/9af28805-41b4-4416-9b42-bdf30c63dca3): it controls individual coefficient energies before any positive/negative pair cancellation. A native Green-weighted comparison within a prescribed support endpoint remains a separate transfer obligation.
--
--   **Formalization Note.** The prescribed function is extended to $\mathbb C$ in the statement, but only its values on $S$ are used. The sum is represented over the actual critical-zero subtype with terms in $S$ set to zero. This is the arbitrary-packet coefficient-energy theorem from the independently checked repository construction, restated with its energy definition expanded.
-- source:
--   Jean-Francois Burnol, The Explicit Formula in simple terms, https://arxiv.org/abs/math/9810169v2, pp. 5-6, finite interpolation and convolution amplification. The squared-coefficient energy conclusion is a proved strengthening of that construction, not a quoted theorem: the linear explicit formula and strip envelope supply individual weighted square summability. Repository theorem ConnesRZEnergy.coefficient_energy_localization and closed explicit formula; existing P2M criterion root 9af28805-41b4-4416-9b42-bdf30c63dca3.

import Definitions.Def_ConnesRZ_weil_defs

open Complex
open scoped BigOperators

theorem ConnesRZ.coefficient_energy_localization (S : Finset {s : ℂ // IsCriticalZero s}) (a : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, IsTest g ∧ (∀ ρ ∈ S, mellinHat g ρ.1 = a ρ.1) ∧
      Summable (fun ρ : {s : ℂ // IsCriticalZero s} =>
        if ρ ∈ S then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) ∧
      (∑' ρ : {s : ℂ // IsCriticalZero s},
        if ρ ∈ S then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) < ε := by sorry
