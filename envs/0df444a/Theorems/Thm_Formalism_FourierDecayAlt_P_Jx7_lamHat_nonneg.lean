-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_lamHat_nonneg
-- name    : Formalism.FourierDecayAlt.P.Jx7.lamHat_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:41.931248+00:00
-- url     : https://prove2.me/theorems/5a550ab8-93c7-4325-9ca7-919056128887
-- title:
--   Jx7: lam Hat nonneg
-- statement:
--   The Jx7 construction uses the lam Hat nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L150-L154

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

theorem Formalism.FourierDecayAlt.P.Jx7.lamHat_nonneg (hg : 0 < G.g) (hka : 0 < G.ka) (hC : 0 ≤ C) (hI : 0 < G.lenI) (b s : ℕ) (x : ℝ)
    (hx : 0 ≤ x) : 0 ≤ Sz.lamHat b s C G.ka G.N G.lenI G.g x := by sorry
