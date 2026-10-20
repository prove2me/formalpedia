-- Prove2me | Theorems.Thm_DerivativeChainPrivate_almost_real_row_count
-- name    : DerivativeChainPrivate.almost_real_row_count
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:51:18.876468+00:00
-- url     : https://prove2.me/theorems/42c5a570-06ef-457f-9964-1f5a81dc8d43
-- title:
--   Multiplicity-aware real-root count in every actual derivative row
-- statement:
--   If the proposal product has real coefficients, there is a real polynomial p whose complexification is that product. For every row m between zero and n, the real derivative of order n-m complexifies to the proposal row, has natural degree m, and has at least m minus nonrealCount a real roots counting multiplicities. No disk assumption is needed.
-- source:
--   Derivative-zero chains: public formalization reference, R31, DerivativeChainPrivate.almost_real_row_count. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_real_coefficients_descent
import Theorems.Thm_DerivativeChainPrivate_real_root_defect_iterate
import Theorems.Thm_DerivativeChainPrivate_root_slot_nonreal_count

set_option autoImplicit false
open DerivativeChainPrivate

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.almost_real_row_count {n : ℕ} (a : Fin n → ℂ) (hr : RealCoefficients a) :
    ∃ p : Polynomial ℝ, p.map Complex.ofRealHom = fromRoots a ∧
      ∀ m : ℕ, m ≤ n →
        ((Polynomial.derivative^[n - m]) p).map Complex.ofRealHom = row a m ∧
        ((Polynomial.derivative^[n - m]) p).natDegree = m ∧
        m - nonrealCount a ≤ ((Polynomial.derivative^[n - m]) p).roots.card := by sorry
