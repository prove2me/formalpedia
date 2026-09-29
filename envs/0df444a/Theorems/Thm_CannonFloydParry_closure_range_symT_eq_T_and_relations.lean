-- Prove2me | Theorems.Thm_CannonFloydParry_closure_range_symT_eq_T_and_relations
-- name    : CannonFloydParry.closure_range_symT_eq_T_and_relations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:45:56.99692+00:00
-- url     : https://prove2.me/theorems/f316b946-fcd1-497f-9e9d-4ed16dc69e60
-- title:
--   Lemma 5.2 — $A$, $B$, $C$ generate $T$ and satisfy relations 1)–6)
-- statement:
--   The maps $A$, $B$, $C$ of the circle generate $T$, and satisfy
--
--   1) $[AB^{-1}, A^{-1}BA] = 1$, 2) $[AB^{-1}, A^{-2}BA^2] = 1$, 3) $C = B(A^{-1}CB)$, 4) $(A^{-1}CB)(A^{-1}BA) = B(A^{-2}CB^2)$, 5) $CA = (A^{-1}CB)^2$, 6) $C^3 = 1$.
--
--   **Formalization Note.** $A$, $B$, $C$ are `symT` of the three symbols. The commutators are written out as $xyx^{-1}y^{-1}$, and products compose right to left, the source's convention; under the opposite order relations 1)–5) fail.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 234, Lemma 5.2

import Mathlib
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem closure_range_symT_eq_T_and_relations :
    Subgroup.closure (Set.range symT) = T ∧
      let a := symT FormalABC.A
      let b := symT FormalABC.B
      let c := symT FormalABC.C
      (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹ = 1 ∧
      (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ = 1 ∧
      c = b * (a⁻¹ * c * b) ∧
      (a⁻¹ * c * b) * (a⁻¹ * b * a) = b * (a⁻¹ ^ 2 * c * b ^ 2) ∧
      c * a = (a⁻¹ * c * b) ^ 2 ∧
      c ^ 3 = 1 := by
  sorry

end CannonFloydParry
