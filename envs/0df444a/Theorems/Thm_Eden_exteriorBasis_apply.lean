-- Prove2me | Theorems.Thm_Eden_exteriorBasis_apply
-- name    : Eden.exteriorBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:12.302343+00:00
-- url     : https://prove2.me/theorems/010e4010-f828-47dd-8813-3bf10ccd7c10
-- title:
--   Eden: exterior Basis apply
-- statement:
--   The Eden construction uses the exterior Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L30-L35
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L30-L35

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.exteriorBasis_apply (k : ℕ) (s : ExteriorIndex k) :
    exteriorBasis k s = exteriorPower.ιMulti_family ℝ k
      (EuclideanSpace.basisFun (Fin 5) ℝ) s := by sorry
