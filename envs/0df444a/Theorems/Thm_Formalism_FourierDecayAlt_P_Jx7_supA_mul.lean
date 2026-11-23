-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_supA_mul
-- name    : Formalism.FourierDecayAlt.P.Jx7.supA_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:46.427402+00:00
-- url     : https://prove2.me/theorems/e8dbff28-18f6-4cd4-b9ad-5c7288561f94
-- title:
--   Jx7: sup A mul
-- statement:
--   The Jx7 construction uses the sup A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L126-L130

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

theorem Formalism.FourierDecayAlt.P.Jx7.supA_mul (hg : 0 < G.g) (hka : 0 < G.ka) (p : Prop) [Decidable p] (w : ι) :
    G.g ^ G.m * ((G.ka ^ (G.m - 1))⁻¹ * supA G de de' T T' l (decide p) w) = sp G de de' T T' l p w := by sorry
