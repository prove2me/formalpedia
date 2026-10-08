-- Prove2me | Theorems.Thm_ConnesRZ_quartet_coefficient_energy_separation
-- name    : ConnesRZ.quartet_coefficient_energy_separation
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T22:23:56.093557+00:00
-- url     : https://prove2.me/theorems/9cc65423-515b-4486-a686-ee1b41b63731
-- title:
--   Actual-zero quartet separation with full complementary coefficient-energy control
-- statement:
--   Let $s$ be an actual zero of the Riemann zeta function with $0<\operatorname{Re}s<1$ and $\operatorname{Re}s\ne1/2$. Let
--   $$Q=\{s,\bar s,1-\bar s,1-s\}$$
--   be its fixed reflection/conjugation orbit, and let $m_\rho$ be each actual zero's analytic multiplicity. There is a smooth compactly supported test function $g:\mathbb R\to\mathbb C$ with shifted Mellin transform $\widehat g(z)=\int g(t)e^{(z-1/2)t}\,dt$ such that
--   $$\widehat g(z)=\begin{cases}1&\operatorname{Re}z=\operatorname{Re}s,\\-1&\operatorname{Re}z\ne\operatorname{Re}s\end{cases}\quad(z\in Q).$$
--   For the same test function, the complete complementary individual coefficient-energy family is unconditionally summable and
--   $$\sum_{\rho\notin Q}m_\rho|\widehat g(\rho)|^2<\tfrac12,\qquad
--   \sum_{\rho\notin Q}\left|m_\rho\widehat g(\rho)\overline{\widehat g(1-\bar\rho)}\right|<\tfrac12,\qquad
--   \operatorname{Re}W(g*g^*)<-\tfrac12.$$
--   Both sums retain every other actual critical-strip zeta zero and its multiplicity. The selected set remains unchanged and no simple-zero assumption is made; the set notation also handles a collapsed orbit.
--
--   This strengthens the [existing Weil positivity criterion](https://prove2.me/theorems/9af28805-41b4-4416-9b42-bdf30c63dca3): the raw complementary coefficient energy is strictly smaller than the full arithmetic negative margin. It assumes neither RH nor Weil positivity. No support endpoint is prescribed; the native fixed-window Green-weighted marker attachment and its quantitative inequality remain separate obligations.
--
--   **Formalization Note.** The public statement expands the packet and coefficient-energy definitions, retaining the exact existing Connes carrier and arithmetic distribution. Complementary sums are represented over the actual critical-zero subtype with selected terms set to zero.
-- source:
--   Jean-Francois Burnol, The Explicit Formula in simple terms, https://arxiv.org/abs/math/9810169v2, pp. 5-6, finite interpolation and convolution amplification; A. Connes, Noncommutative geometry and the Riemann zeta function, section 3, pp. 15 and 22. The joint individual-energy/full-tail margin is a proved strengthening of the construction, not a quoted theorem. Repository ConnesRZClosed.quartet_coefficient_energy_separation, with all explicit-formula proof bodies independently rebuilt. Related P2M root 9af28805-41b4-4416-9b42-bdf30c63dca3.

import Definitions.Def_ConnesRZ_weil_defs

open Complex
open scoped BigOperators

theorem ConnesRZ.quartet_coefficient_energy_separation (s : ℂ) (hs : IsCriticalZero s) (hoff : s.re ≠ 1 / 2) :
    let Q : Finset ℂ := {s, (starRingEnd ℂ) s, 1 - (starRingEnd ℂ) s, 1 - s}
    ∃ g : ℝ → ℂ, IsTest g ∧
      (∀ z ∈ Q, mellinHat g z = if z.re = s.re then 1 else -1) ∧
      Summable (fun ρ : {z : ℂ // IsCriticalZero z} =>
        if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) ∧
      (∑' ρ : {z : ℂ // IsCriticalZero z},
        if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) < 1 / 2 ∧
      (∑' ρ : {z : ℂ // IsCriticalZero z},
        ‖if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℂ) *
          (mellinHat g ρ.1 * (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))‖) < 1 / 2 ∧
      (weilDistribution (conv g (starInv g))).re < -(1 / 2) := by sorry
