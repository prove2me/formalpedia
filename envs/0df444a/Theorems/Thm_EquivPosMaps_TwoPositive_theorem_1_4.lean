-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_theorem_1_4
-- name    : EquivPosMaps.TwoPositive.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:43.187972+00:00
-- url     : https://prove2.me/theorems/3669b892-624b-4d34-afc4-559289a5e327
-- title:
--   Theorem 1.4 (1)⇔(2): Choi criterion
-- statement:
--   Let $\Psi:M_{d_1}(\mathbb C)\to M_{d_2}(\mathbb C)$ be a complex-linear map, and let $C_\Psi=\sum_{i,j}e_{ij}\otimes\Psi(e_{ij})$ be its Choi matrix. Then
--
--   $$
--   \Psi\text{ is completely positive}\quad\Longleftrightarrow\quad C_\Psi\geq0.
--   $$
--
--   This links the operational all-ancilla definition of complete positivity to a finite matrix inequality. The paper's printed item (3), a Kraus representation, is omitted because its operator types and numerical bound are malformed; the equivalence of items (1) and (2) is the part used in this mission.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, p. 3, Theorem 1.4 (1)⇔(2)

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Theorem 1.4 (1) ↔ (2), p. 3: Choi's criterion. -/
theorem theorem_1_4 (d₁ d₂ : ℕ)
    (Φ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ) :
    QAlgorithms.Entanglement.IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by sorry

end EquivPosMaps.TwoPositive
