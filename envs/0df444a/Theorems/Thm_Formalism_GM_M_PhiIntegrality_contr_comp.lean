-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_comp
-- name    : Formalism.GM.M.PhiIntegrality.contr_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:38.290794+00:00
-- url     : https://prove2.me/theorems/336054b9-ed7f-4915-9fc8-f2e20915c3a7
-- title:
--   Phi Integrality: contr comp
-- statement:
--   The Phi Integrality construction uses the contr comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L128-L134

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

theorem Formalism.GM.M.PhiIntegrality.contr_comp {C C' : ℝ} {T T' : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]}
    (hC : 0 ≤ C) (h : Contr C T) (h' : Contr C' T') : Contr (C * C') (T' * T) := by sorry
