-- Prove2me | Theorems.Thm_Eden_spectralProduct_zero
-- name    : Eden.spectralProduct_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:51.128619+00:00
-- url     : https://prove2.me/theorems/cd99fc16-3e64-4e4c-96ff-e49006b01f64
-- title:
--   Eden: spectral Product zero
-- statement:
--   The Eden construction uses the spectral Product zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L67-L73
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L67-L73

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectralProduct_zero (n : ℕ) (a : ℕ → ℝ) : spectralProduct n a 0 = 1 := by sorry
