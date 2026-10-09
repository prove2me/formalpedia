-- Prove2me | Theorems.Thm_BMV2017_psiEnd_entangled
-- name    : BMV2017.psiEnd_entangled
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-08T23:53:53.437813+00:00
-- url     : https://prove2.me/theorems/6f9b000e-06e0-45b8-9352-51d8b041a11e
-- title:
--   p. 2, Eq. (2) — the gravitationally evolved state is entangled unless $\Delta\phi_{LR}+\Delta\phi_{RL}\in 2\pi\mathbb Z$
-- statement:
--   Let $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12\big(|00\rangle+e^{i\alpha}|01\rangle+e^{i\beta}|10\rangle+|11\rangle\big)$ (basis $|0\rangle=|L\rangle$ or $|{\uparrow}\rangle$, $|1\rangle=|R\rangle$ or $|{\downarrow}\rangle$; first factor = mass 1; $\alpha=\Delta\phi_{LR}$, $\beta=\Delta\phi_{RL}$; global phase omitted). If $\alpha+\beta\neq 2n\pi$ for every integer $n$, then $\psi_{\mathrm{End}}(\alpha,\beta)$ is not a product vector: there are no $u,w\in\mathbb C^2$ with $\psi_{\mathrm{End}}(\alpha,\beta)=u\otimes w$.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2, Eqs. (1)–(2) and the paragraph following them

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BMV2017_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BMV2017

theorem psiEnd_entangled (α β : ℝ) (h : ∀ n : ℤ, α + β ≠ 2 * Real.pi * n) :
    ¬ IsProductVector (psiEnd α β) := by sorry

end BMV2017
