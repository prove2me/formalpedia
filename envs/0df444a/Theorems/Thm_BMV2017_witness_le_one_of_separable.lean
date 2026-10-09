-- Prove2me | Theorems.Thm_BMV2017_witness_le_one_of_separable
-- name    : BMV2017.witness_le_one_of_separable
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-08T23:56:08.244428+00:00
-- url     : https://prove2.me/theorems/b2ef101d-0637-40f6-8a17-1726d15d9efd
-- title:
--   p. 3 — the spin entanglement witness: $\mathcal W\le 1$ on every separable two-qubit state
-- statement:
--   Let $\rho$ be a **separable** two-qubit state: $\rho=\sum_{i=1}^n p_i\,\rho_i^{(1)}\otimes\rho_i^{(2)}$ with $p_i\ge0$, $\sum_ip_i=1$ and $\rho_i^{(1)},\rho_i^{(2)}$ qubit density matrices. Then
--   $$\mathcal W(\rho)=\big|\operatorname{Tr}\rho(\sigma_x\otimes\sigma_z)-\operatorname{Tr}\rho(\sigma_y\otimes\sigma_y)\big|\le 1 .$$
--   Equivalently, $\mathcal W(\rho)>1$ certifies that $\rho$ is entangled.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 3: 'W = |⟨σx(1)⊗σz(2)⟩ − ⟨σy(1)⊗σy(2)⟩|. If W is found to exceed unity then the state is proven to be entangled'

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BMV2017_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BMV2017

theorem witness_le_one_of_separable (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
    (hρ : IsSeparable ρ) : witness ρ ≤ 1 := by sorry

end BMV2017
