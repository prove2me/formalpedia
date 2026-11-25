-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_vol
-- name    : Formalism.HermitianLatticeCounting.P.s5b7_vol
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:48.895822+00:00
-- url     : https://prove2.me/theorems/d6d422ee-e172-4b31-bcf8-0fd16b97f4ae
-- title:
--   P: s5b7 vol
-- statement:
--   The P construction uses the s5b7 vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L784-L906
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L784-L906

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.s5b7_vol (R : ℝ) (hR : 0 < R) : ∀ (r d : ℕ), r ≤ d → ∀ t : ℝ, 0 ≤ t →
    volume (s5b7_A R d r t) ≤ ENNReal.ofReal (t ^ (2 * (d - r)) * R ^ (2 * r ^ 2) *
      Real.pi ^ (r * d) / ((d - r).factorial : ℝ) ^ r) := by sorry
