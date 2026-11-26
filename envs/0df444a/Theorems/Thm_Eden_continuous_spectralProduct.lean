-- Prove2me | Theorems.Thm_Eden_continuous_spectralProduct
-- name    : Eden.continuous_spectralProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:44.473234+00:00
-- url     : https://prove2.me/theorems/3010a59e-ffdb-4bbb-8a04-5455725c58be
-- title:
--   Eden: continuous spectral Product
-- statement:
--   The Eden construction uses the continuous spectral Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L83-L89
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L83-L89

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.continuous_spectralProduct {n : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i < n, a i ≠ 0) : Continuous (spectralProduct n a) := by sorry
