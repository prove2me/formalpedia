-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NU_prod_X_eq
-- name    : Formalism.NormUnitaryCountingLemmas.NU.prod_X_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:06.426785+00:00
-- url     : https://prove2.me/theorems/6b31d69b-794f-4758-8c2a-b3bde5f46330
-- title:
--   NU: prod X eq
-- statement:
--   The NU construction uses the prod X eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormUnitary.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormUnitary.lean#L21-L23

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem Formalism.NormUnitaryCountingLemmas.NU.prod_X_eq {R : Type*} [CommSemiring R] {d : ℕ} (t : Fin d → σ) :
    (∏ m, (X (t m) : MvPolynomial σ R)) = monomial (cnt t) 1 := by sorry
