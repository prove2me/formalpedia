-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sym_mul
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_sym_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:33.644692+00:00
-- url     : https://prove2.me/theorems/c66aed96-8476-4848-91e2-01b75d15b17b
-- title:
--   Column Families: qs sym mul
-- statement:
--   The Column Families construction uses the qs sym mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L22-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L22-L47

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_sym_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A)
    (m : ι → Fin n) (β : Fin n → ℕ) (hβ : ∀ x, qs_cnt m x = β x) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (∏ x : Fin n, (∑ a : Fin n, MvPolynomial.C (G a x) * X a) ^ (β x)) =
      ∑ a : ι → Fin n, if (∀ x, qs_cnt a x = α x) then ∏ c, G (a c) (m c) else 0 := by sorry
