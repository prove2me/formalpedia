-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_thrS_nonneg
-- name    : Formalism.FourierDecayAlt.P.Jx7.thrS_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:16.669005+00:00
-- url     : https://prove2.me/theorems/91c7297d-3b03-4350-9434-6cd7c84c60fd
-- title:
--   Jx7: thr S nonneg
-- statement:
--   The Jx7 construction uses the thr S nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L142-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L142-L148

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)

theorem Formalism.FourierDecayAlt.P.Jx7.thrS_nonneg (hg : 0 < G.g) (hka : 0 < G.ka) (hC : 0 ≤ C) (hI : 0 < G.lenI) (b s : ℕ) (w : ι) :
    0 ≤ thrS G C de de' T T' l b s w := by sorry
