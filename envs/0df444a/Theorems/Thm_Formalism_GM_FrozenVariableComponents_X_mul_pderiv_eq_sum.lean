-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_X_mul_pderiv_eq_sum
-- name    : Formalism.GM.FrozenVariableComponents.X_mul_pderiv_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:54.787531+00:00
-- url     : https://prove2.me/theorems/343b2a9d-307a-4918-8d14-1a01038409a1
-- title:
--   Frozen Variable Components: X mul pderiv eq sum
-- statement:
--   The Frozen Variable Components construction uses the X mul pderiv eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L390-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L390-L396

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K] {σ : Type*}

theorem Formalism.GM.FrozenVariableComponents.X_mul_pderiv_eq_sum [DecidableEq σ] (a b : σ) (F : MvPolynomial σ K) :
    X a * pderiv b F = ∑ m0 ∈ F.support,
      monomial (m0 - Finsupp.single b 1 + Finsupp.single a 1) (coeff m0 F * m0 b) := by sorry
