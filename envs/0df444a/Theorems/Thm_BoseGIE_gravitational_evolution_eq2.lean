-- Prove2me | Theorems.Thm_BoseGIE_gravitational_evolution_eq2
-- name    : BoseGIE.gravitational_evolution_eq2
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-11T19:25:20.578083+00:00
-- url     : https://prove2.me/theorems/b5c23001-ec9b-45b5-8474-2c6f4f60e325
-- title:
--   p. 2, Eqs. (1)–(2) — gravitational evolution of the two superposed masses
-- statement:
--   Let $G,m_1,m_2,\hbar,\tau>0$ and $0<\Delta x<d$. The branch separations are $r_{LL}=r_{RR}=d$, $r_{LR}=d+\Delta x$, $r_{RL}=d-\Delta x$ (first index = position of mass 1), with Newtonian energies $E_{jk}=-Gm_1m_2/r_{jk}$. Let $\psi_0=\tfrac12\sum_{j,k}|jk\rangle$ (Eq. (1)), $\phi=\frac{Gm_1m_2\tau}{\hbar d}$, $\phi_{LR}=\frac{Gm_1m_2\tau}{\hbar(d+\Delta x)}$, $\phi_{RL}=\frac{Gm_1m_2\tau}{\hbar(d-\Delta x)}$. Then (i) evolving each branch by $e^{-iE_{jk}\tau/\hbar}$ gives Eq. (2):
--   $$\big(e^{-iE_{jk}\tau/\hbar}\,(\psi_0)_{jk}\big)_{j,k}=e^{i\phi}\,\psi_{\mathrm{End}}(\phi_{LR}-\phi,\ \phi_{RL}-\phi),$$
--   where $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12\big(|LL\rangle+e^{i\alpha}|LR\rangle+e^{i\beta}|RL\rangle+|RR\rangle\big)$ (first factor = mass 1; $\alpha=\Delta\phi_{LR}$, $\beta=\Delta\phi_{RL}$; global phase omitted); and (ii) $\Delta\phi_{LR}+\Delta\phi_{RL}=(\phi_{LR}-\phi)+(\phi_{RL}-\phi)>0$.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2, Eqs. (1)–(2) and the phase formulas below Eq. (2); p. 4, estimate of ΔφRL + ΔφLR

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BoseGIE

theorem gravitational_evolution_eq2 (G m₁ m₂ hbar τ d Δx : ℝ) (hG : 0 < G) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hhbar : 0 < hbar) (hτ : 0 < τ) (hΔx : 0 < Δx) (hd : Δx < d) :
    let r : Qubit → Qubit → ℝ := ![![d, d + Δx], ![d - Δx, d]]
    let E : Qubit × Qubit → ℝ := fun p => -(G * m₁ * m₂) / r p.1 p.2
    let ψ₀ : Qubit × Qubit → ℂ := fun _ => 1 / 2
    let φ : ℝ := G * m₁ * m₂ * τ / (hbar * d)
    let φLR : ℝ := G * m₁ * m₂ * τ / (hbar * (d + Δx))
    let φRL : ℝ := G * m₁ * m₂ * τ / (hbar * (d - Δx))
    (fun p => Complex.exp (-((E p * τ / hbar : ℝ) : ℂ) * Complex.I) * ψ₀ p) =
        Complex.exp ((φ : ℂ) * Complex.I) • psiEnd (φLR - φ) (φRL - φ) ∧
      0 < (φLR - φ) + (φRL - φ) := by sorry

end BoseGIE
