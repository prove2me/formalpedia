-- Prove2me | Theorems.Thm_Eden_supremumExponentSum_nonneg
-- name    : Eden.supremumExponentSum_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:43.786691+00:00
-- url     : https://prove2.me/theorems/f1afec7a-8d18-5397-8a88-e7479f395f5b
-- title:
--   Eden: supremum Exponent Sum nonneg
-- statement:
--   The Eden construction uses the supremum Exponent Sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L130-L138
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L130-L138

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremumExponentSum_nonneg {c : ℝ} (hc : 4 < c) {k : ℕ} (hk : k ≤ 4) :
    0 ≤ supremumExponentSum c k := by sorry
