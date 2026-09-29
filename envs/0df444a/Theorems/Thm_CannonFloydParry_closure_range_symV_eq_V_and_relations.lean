-- Prove2me | Theorems.Thm_CannonFloydParry_closure_range_symV_eq_V_and_relations
-- name    : CannonFloydParry.closure_range_symV_eq_V_and_relations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:22:54.859229+00:00
-- url     : https://prove2.me/theorems/e8f1b2e6-a7cb-4956-99cb-081db9fb8ab7
-- title:
--   Lemma 6.1 — $A$, $B$, $C$, $\pi_0$ generate $V$ and satisfy relations 1)–14)
-- statement:
--   The maps $A$, $B$, $C$, $\pi_0$ of the circle generate $V$, and, with $X_n$, $C_n$, $\pi_n$ the words of p. 241 read as maps: 1) $[AB^{-1}, X_2] = 1$, 2) $[AB^{-1}, X_3] = 1$, 3) $C_1 = BC_2$, 4) $C_2X_2 = BC_3$, 5) $C_1A = C_2^2$, 6) $C_1^3 = 1$, 7) $\pi_1^2 = 1$, 8) $\pi_1\pi_3 = \pi_3\pi_1$, 9) $(\pi_2\pi_1)^3 = 1$, 10) $X_3\pi_1 = \pi_1X_3$, 11) $\pi_1X_2 = B\pi_2\pi_1$, 12) $\pi_2B = B\pi_3$, 13) $\pi_1C_3 = C_3\pi_2$, 14) $(\pi_1C_2)^3 = 1$.
--
--   **Formalization Note.** Commutators are written out as $xyx^{-1}y^{-1}$; products compose right to left.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 241, Lemma 6.1

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem closure_range_symV_eq_V_and_relations :
    Subgroup.closure (Set.range symV) = V ∧
      let a := symV FormalV.A
      let b := symV FormalV.B
      (a * b⁻¹) * XV 2 * (a * b⁻¹)⁻¹ * (XV 2)⁻¹ = 1 ∧
      (a * b⁻¹) * XV 3 * (a * b⁻¹)⁻¹ * (XV 3)⁻¹ = 1 ∧
      CV 1 = b * CV 2 ∧
      CV 2 * XV 2 = b * CV 3 ∧
      CV 1 * a = CV 2 ^ 2 ∧
      CV 1 ^ 3 = 1 ∧
      piV 1 ^ 2 = 1 ∧
      piV 1 * piV 3 = piV 3 * piV 1 ∧
      (piV 2 * piV 1) ^ 3 = 1 ∧
      XV 3 * piV 1 = piV 1 * XV 3 ∧
      piV 1 * XV 2 = b * piV 2 * piV 1 ∧
      piV 2 * b = b * piV 3 ∧
      piV 1 * CV 3 = CV 3 * piV 2 ∧
      (piV 1 * CV 2) ^ 3 = 1 := by
  sorry

end CannonFloydParry
