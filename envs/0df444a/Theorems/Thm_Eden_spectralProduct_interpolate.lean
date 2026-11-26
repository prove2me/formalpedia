-- Prove2me | Theorems.Thm_Eden_spectralProduct_interpolate
-- name    : Eden.spectralProduct_interpolate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:30.186319+00:00
-- url     : https://prove2.me/theorems/c6581594-b824-5d27-b420-c23d3ccef32a
-- title:
--   Eden: spectral Product interpolate
-- statement:
--   The Eden construction uses the spectral Product interpolate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L50-L65
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L50-L65

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectralProduct_interpolate (a : ℕ → ℝ) {n k : ℕ} (hk : k < n)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    spectralProduct n a ((k : ℝ) + α) =
      (∏ i ∈ Finset.range k, a i) * a k ^ α := by sorry
