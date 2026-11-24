-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_inRegion_of_lt
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.inRegion_of_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:12.501786+00:00
-- url     : https://prove2.me/theorems/9801032c-874e-412c-95b9-9ea6d6863dbe
-- title:
--   Logarithmic Integral Bounds: in Region of lt
-- statement:
--   The Logarithmic Integral Bounds construction uses the in Region of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean#L10-L25

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_Statement
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPage
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.inRegion_of_lt {c Z β : ℝ} {q : ℕ} (hc : 0 < c) (hZ : 3 ≤ Z) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Z ^ 2)
    (hβ : 1 - c / 3 / Real.log Z < β) : Formalism.ZeroFreeDirichlet.InRegion c q (β : ℂ) := by sorry
