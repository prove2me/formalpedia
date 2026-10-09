-- Prove2me | Theorems.Thm_BMV2017_reducedPurity_strictAnti
-- name    : BMV2017.reducedPurity_strictAnti
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-08T23:54:16.064628+00:00
-- url     : https://prove2.me/theorems/bdca76d1-b5ac-47da-bebe-0f6dd22e21e4
-- title:
--   p. 2 — entanglement grows monotonically in $\Delta\phi_{LR}+\Delta\phi_{RL}\in[0,\pi]$ and is maximal at $\pi$
-- statement:
--   Let $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12\big(|00\rangle+e^{i\alpha}|01\rangle+e^{i\beta}|10\rangle+|11\rangle\big)$ (basis $|0\rangle=|L\rangle$ or $|{\uparrow}\rangle$, $|1\rangle=|R\rangle$ or $|{\downarrow}\rangle$; first factor = mass 1; $\alpha=\Delta\phi_{LR}$, $\beta=\Delta\phi_{RL}$; global phase omitted) and let $\rho_1=\operatorname{Tr}_2|\psi_{\mathrm{End}}\rangle\langle\psi_{\mathrm{End}}|$ be the reduced state of mass 1. Then (i) the purity $\operatorname{Tr}\rho_1^2$ is strictly decreasing in $\alpha+\beta$ on $[0,\pi]$: if $0\le\alpha+\beta<\alpha'+\beta'\le\pi$ then $\operatorname{Tr}\rho_1(\alpha',\beta')^2<\operatorname{Tr}\rho_1(\alpha,\beta)^2$; and (ii) if $\alpha+\beta=\pi$ then $\rho_1=\tfrac12\mathbb 1$ (maximally mixed, i.e. $\psi_{\mathrm{End}}$ is maximally entangled).
--
--   **Formalization Note** The source names no entanglement measure. For pure two-qubit states every standard measure is a monotone function of the reduced-state purity, which is used here.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2, sentence after Eq. (2): 'the entanglement between the masses increases monotonically over ΔφLR + ΔφRL evolving from 0 to π, with the entanglement being maximal for π'

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BMV2017_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BMV2017

theorem reducedPurity_strictAnti :
    (∀ α β α' β' : ℝ, 0 ≤ α + β → α + β < α' + β' → α' + β' ≤ Real.pi →
        reducedPurity (psiEnd α' β') < reducedPurity (psiEnd α β)) ∧
    (∀ α β : ℝ, α + β = Real.pi → ptrace₂ (pureDM (psiEnd α β)) = (1 / 2 : ℂ) • 1) := by sorry

end BMV2017
