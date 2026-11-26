-- Prove2me | Theorems.Thm_Eden_normalized_nonneg_of_factor_subset
-- name    : Eden.normalized_nonneg_of_factor_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:51.503853+00:00
-- url     : https://prove2.me/theorems/982540e7-1f0c-4f4b-926b-75bbf319403c
-- title:
--   Eden: normalized nonneg of factor subset
-- statement:
--   The Eden construction uses the normalized nonneg of factor subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L88-L101
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L88-L101

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.normalized_nonneg_of_factor_subset (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (s : Finset (Fin 5))
    (hs : ∀ j ∈ s, 0 ≤ Real.log (derivativeFactors c t p j))
    (i : Fin 5) (hi : i.val < s.card) : 0 ≤ normalizedLogSingularValues c t p i := by sorry
