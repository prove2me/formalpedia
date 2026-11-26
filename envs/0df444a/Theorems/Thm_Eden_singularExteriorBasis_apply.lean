-- Prove2me | Theorems.Thm_Eden_singularExteriorBasis_apply
-- name    : Eden.singularExteriorBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:34.453793+00:00
-- url     : https://prove2.me/theorems/4ef70dbf-590d-5da5-a2d9-eaba1c4e72b4
-- title:
--   Eden: singular Exterior Basis apply
-- statement:
--   The Eden construction uses the singular Exterior Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L53-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L53-L58

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden

theorem Eden.singularExteriorBasis_apply (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : singularExteriorBasis k A s =
      exteriorPower.ιMulti_family ℝ k (singularVectorBasis A) s := by sorry
