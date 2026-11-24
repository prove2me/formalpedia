-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_D
-- name    : Formalism.GM.M.PhiIntegrality.contr_D
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:44.322236+00:00
-- url     : https://prove2.me/theorems/b9aaf40e-0282-4a80-9ff5-ae9c01a2a7ed
-- title:
--   Phi Integrality: contr D
-- statement:
--   The Phi Integrality construction uses the contr D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L136-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L136-L150

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

theorem Formalism.GM.M.PhiIntegrality.contr_D (i j : σ) (k : ℕ) :
    Contr 1 ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv j).toLinearMap) ^ k)) := by sorry
