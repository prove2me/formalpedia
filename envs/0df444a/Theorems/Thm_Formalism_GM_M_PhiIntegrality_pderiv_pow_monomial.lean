-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_pderiv_pow_monomial
-- name    : Formalism.GM.M.PhiIntegrality.pderiv_pow_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:01.028809+00:00
-- url     : https://prove2.me/theorems/45fdb6f8-14e1-4871-918b-7faf43e7a631
-- title:
--   Phi Integrality: pderiv pow monomial
-- statement:
--   The Phi Integrality construction uses the pderiv pow monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L101-L112

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

theorem Formalism.GM.M.PhiIntegrality.pderiv_pow_monomial (i : σ) (s : ℕ) (m : σ →₀ ℕ) (a : ℚ_[p]) :
    (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ s)
      (monomial m a)) = monomial (m - Finsupp.single i s) (a * ((m i).descFactorial s : ℚ_[p])) := by sorry
