-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mollM_norm_le
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mollM_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:21.150966+00:00
-- url     : https://prove2.me/theorems/f690988d-6115-426f-8b48-830c4ab070bf
-- title:
--   ZD: moll M norm le
-- statement:
--   The ZD construction uses the moll M norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDetect.lean#L20-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDetect.lean#L20-L40

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDetect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
open scoped ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mollM_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 0 ≤ s.re) (Y : ℕ) :
    ‖∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ Y := by sorry
