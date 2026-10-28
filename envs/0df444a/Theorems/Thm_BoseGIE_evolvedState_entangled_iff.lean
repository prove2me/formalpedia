-- Prove2me | Theorems.Thm_BoseGIE_evolvedState_entangled_iff
-- name    : BoseGIE.evolvedState_entangled_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-11T19:27:54.35416+00:00
-- url     : https://prove2.me/theorems/29c59491-1da0-403c-af4a-100b7107d3a8
-- title:
--   p. 2 — the gravitationally evolved state is entangled iff $\Delta\phi_{LR}+\Delta\phi_{RL}\notin 2\pi\mathbb Z$
-- statement:
--   Let $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12\big(|LL\rangle+e^{i\alpha}|LR\rangle+e^{i\beta}|RL\rangle+|RR\rangle\big)$ (first factor = mass 1; $\alpha=\Delta\phi_{LR}$, $\beta=\Delta\phi_{RL}$; global phase omitted) and $\rho=|\psi_{\mathrm{End}}\rangle\langle\psi_{\mathrm{End}}|$. Then $\rho$ is **entangled**, i.e. not separable (not a finite convex combination $\sum_i p_i\,\rho_i^{(1)}\otimes\rho_i^{(2)}$ of products of qubit density matrices), if and only if $\alpha+\beta\neq 2n\pi$ for every integer $n$.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2, paragraph after Eq. (2): '... cannot be factorized and is thereby in an entangled state of the two orbital qubits'

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BoseGIE

theorem evolvedState_entangled_iff (α β : ℝ) :
    ¬ IsSeparable (pureDM (psiEnd α β)) ↔ ∀ n : ℤ, α + β ≠ 2 * Real.pi * n := by sorry

end BoseGIE
