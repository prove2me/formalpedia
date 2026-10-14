-- Prove2me | Theorems.Thm_BoseGIE_reducedPurity_strictAnti
-- name    : BoseGIE.reducedPurity_strictAnti
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-11T19:27:25.79509+00:00
-- url     : https://prove2.me/theorems/e8227413-8d38-4a39-86ef-214c1eedab20
-- title:
--   p. 2 — entanglement grows monotonically as $\Delta\phi_{LR}+\Delta\phi_{RL}$ goes from $0$ to $\pi$, maximal at $\pi$
-- statement:
--   Let $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12\big(|LL\rangle+e^{i\alpha}|LR\rangle+e^{i\beta}|RL\rangle+|RR\rangle\big)$ (first factor = mass 1; $\alpha=\Delta\phi_{LR}$, $\beta=\Delta\phi_{RL}$; global phase omitted) and let $\rho_1=\operatorname{Tr}_2|\psi_{\mathrm{End}}\rangle\langle\psi_{\mathrm{End}}|$ be the reduced state of mass 1. Then (i) if $0\le\alpha+\beta<\alpha'+\beta'\le\pi$, the purity satisfies $\operatorname{Tr}\rho_1(\alpha',\beta')^2<\operatorname{Tr}\rho_1(\alpha,\beta)^2$; and (ii) if $\alpha+\beta=\pi$ then $\rho_1=\tfrac12\mathbb 1$ (maximally mixed, so $\psi_{\mathrm{End}}$ is maximally entangled).
--
--   **Formalization Note** The source names no entanglement measure. For pure two-qubit states every standard measure is a monotone function of the reduced-state purity, which is used here.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2, paragraph after Eq. (2)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BoseGIE

theorem reducedPurity_strictAnti :
    (∀ α β α' β' : ℝ, 0 ≤ α + β → α + β < α' + β' → α' + β' ≤ Real.pi →
        reducedPurity (psiEnd α' β') < reducedPurity (psiEnd α β)) ∧
    (∀ α β : ℝ, α + β = Real.pi → ptrace₂ (pureDM (psiEnd α β)) = (1 / 2 : ℂ) • 1) := by sorry

end BoseGIE
