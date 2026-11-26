-- Prove2me | Theorems.Thm_Eden_singularValueFunction_interpolate
-- name    : Eden.singularValueFunction_interpolate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:28.537802+00:00
-- url     : https://prove2.me/theorems/8d42a157-2d6c-422c-af21-9b9c3e77d5d5
-- title:
--   Eden: singular Value Function interpolate
-- statement:
--   The Eden construction uses the singular Value Function interpolate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L99-L103
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L99-L103

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_interpolate (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    singularValueFunction A ((k : ℝ) + α) =
      (∏ i ∈ Finset.range k, A.singularValues i) * A.singularValues k ^ α := by sorry
