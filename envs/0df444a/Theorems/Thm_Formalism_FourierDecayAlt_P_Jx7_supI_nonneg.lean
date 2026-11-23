-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_supI_nonneg
-- name    : Formalism.FourierDecayAlt.P.Jx7.supI_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:18.500872+00:00
-- url     : https://prove2.me/theorems/c4c4cfeb-6e00-41c8-b810-e00d5f518c5f
-- title:
--   Jx7: sup I nonneg
-- statement:
--   The Jx7 construction uses the sup I nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L101-L107

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

theorem Formalism.FourierDecayAlt.P.Jx7.supI_nonneg (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (w : ι) : 0 ≤ G.supI de de' T T' l w := by sorry
