-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_divDeriv
-- name    : Formalism.GM.M.PhiIntegrality.contr_divDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:45.820567+00:00
-- url     : https://prove2.me/theorems/3eb35eec-88dc-4f30-9fc3-59a0da70e842
-- title:
--   Phi Integrality: contr div Deriv
-- statement:
--   The Phi Integrality construction uses the contr div Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L117-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L117-L126

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

theorem Formalism.GM.M.PhiIntegrality.contr_divDeriv (i : σ) (s : ℕ) :
    Contr 1 (((s.factorial : ℚ_[p]))⁻¹ •
      ((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ s)) := by sorry
