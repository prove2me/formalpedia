-- Prove2me | Theorems.Thm_Formalism_HF_P_quadDiscr_ne_one
-- name    : Formalism.HF.P.quadDiscr_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:48.724583+00:00
-- url     : https://prove2.me/theorems/59e1dca2-2ff1-4224-86b2-1bd5f00d4a2c
-- title:
--   P: quad Discr ne one
-- statement:
--   The P construction uses the quad Discr ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/QuadDiscr.lean#L17-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/QuadDiscr.lean#L17-L91

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial Matrix
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.quadDiscr_ne_one (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) : discr K = a := by sorry
