-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobiSym_prod_left
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobiSym_prod_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:12.980799+00:00
-- url     : https://prove2.me/theorems/37cda5d8-eafd-4b2b-98c9-a693ef93b8ce
-- title:
--   Logarithmic Integral Bounds: jacobi Sym prod left
-- statement:
--   The Logarithmic Integral Bounds construction uses the jacobi Sym prod left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L38-L42

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ) :
    jacobiSym (∏ i ∈ s, f i) b = ∏ i ∈ s, jacobiSym (f i) b := by sorry
