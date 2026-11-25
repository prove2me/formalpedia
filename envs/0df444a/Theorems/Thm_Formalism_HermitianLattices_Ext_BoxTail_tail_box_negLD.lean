-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_box_negLD
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_box_negLD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:12.955459+00:00
-- url     : https://prove2.me/theorems/53b0cd2d-046f-4b81-a362-ea16a1a0c260
-- title:
--   Box Tail: tail box neg LD
-- statement:
--   The Box Tail construction uses the tail box neg LD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean#L35-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean#L35-L119

import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLemmaLfunctionZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_box_negLD (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ →
      ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
        ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ K * Real.log Q := by sorry
