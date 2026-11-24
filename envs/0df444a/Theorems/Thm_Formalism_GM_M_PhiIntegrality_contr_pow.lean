-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_pow
-- name    : Formalism.GM.M.PhiIntegrality.contr_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:15.636063+00:00
-- url     : https://prove2.me/theorems/48a0f512-31ff-41e2-9ac1-24a1940732b7
-- title:
--   Phi Integrality: contr pow
-- statement:
--   The Phi Integrality construction uses the contr pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L162-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L162-L171

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

theorem Formalism.GM.M.PhiIntegrality.contr_pow {C : ℝ} (hC : 0 ≤ C) {T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]}
    (h : Contr C T) (j : ℕ) : Contr (C ^ j) (T ^ j) := by sorry
