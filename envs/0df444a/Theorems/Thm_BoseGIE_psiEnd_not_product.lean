-- Prove2me | Theorems.Thm_BoseGIE_psiEnd_not_product
-- name    : BoseGIE.psiEnd_not_product
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-11T19:26:57.363652+00:00
-- url     : https://prove2.me/theorems/78642892-82d6-43c7-9304-f1aefbc24cd0
-- title:
--   p. 2 — $|\Psi(t=\tau)\rangle$ cannot be factorized when $\Delta\phi_{LR}+\Delta\phi_{RL}\neq 2n\pi$
-- statement:
--   Let $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12\big(|LL\rangle+e^{i\alpha}|LR\rangle+e^{i\beta}|RL\rangle+|RR\rangle\big)$ (first factor = mass 1; $\alpha=\Delta\phi_{LR}$, $\beta=\Delta\phi_{RL}$; global phase omitted). If $\alpha+\beta\neq 2n\pi$ for every integer $n$, then $\psi_{\mathrm{End}}(\alpha,\beta)$ is not a product vector: there are no $u,w\in\mathbb C^2$ with $\psi_{\mathrm{End}}(\alpha,\beta)_{jk}=u_j w_k$ for all $j,k$.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2, paragraph after Eq. (2)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BoseGIE

theorem psiEnd_not_product (α β : ℝ) (h : ∀ n : ℤ, α + β ≠ 2 * Real.pi * n) :
    ¬ IsProductVector (psiEnd α β) := by sorry

end BoseGIE
