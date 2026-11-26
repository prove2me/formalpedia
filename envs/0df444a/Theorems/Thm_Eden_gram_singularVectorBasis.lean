-- Prove2me | Theorems.Thm_Eden_gram_singularVectorBasis
-- name    : Eden.gram_singularVectorBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:42.037171+00:00
-- url     : https://prove2.me/theorems/4c123f64-5ade-5b51-a560-06ba487f369c
-- title:
--   Eden: gram singular Vector Basis
-- statement:
--   The Eden construction uses the gram singular Vector Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L74-L78
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L74-L78

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden

theorem Eden.gram_singularVectorBasis (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (i : Fin 5) :
    (A.adjoint ∘ₗ A) (singularVectorBasis A i) =
      A.singularValues i ^ 2 • singularVectorBasis A i := by sorry
