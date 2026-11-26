-- Prove2me | Theorems.Thm_Eden_spectralProduct_top
-- name    : Eden.spectralProduct_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:39.50881+00:00
-- url     : https://prove2.me/theorems/a9325329-f0b5-4ba2-8896-f16b7f186132
-- title:
--   Eden: spectral Product top
-- statement:
--   The Eden construction uses the spectral Product top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L75-L81
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L75-L81

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectralProduct_top (n : ℕ) (a : ℕ → ℝ) :
    spectralProduct n a n = ∏ i ∈ Finset.range n, a i := by sorry
