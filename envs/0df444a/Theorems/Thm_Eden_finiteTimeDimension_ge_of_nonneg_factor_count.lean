-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_ge_of_nonneg_factor_count
-- name    : Eden.finiteTimeDimension_ge_of_nonneg_factor_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:00.174709+00:00
-- url     : https://prove2.me/theorems/f3f9bdc7-bb11-4cac-b31d-306d854a7c51
-- title:
--   Eden: finite Time Dimension ge of nonneg factor count
-- statement:
--   The Eden construction uses the finite Time Dimension ge of nonneg factor count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L33-L52
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L33-L52

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_ge_of_nonneg_factor_count (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) {k : ℕ} (hk : k ≤ 5)
    (hcount : k ≤ (Finset.univ.filter
      (fun i : Fin 5 => 0 ≤ Real.log (derivativeFactors c t p i) / t)).card) :
    (k : ℝ) ≤ finiteTimeDimension c t p := by sorry
