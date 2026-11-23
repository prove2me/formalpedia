-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_memP
-- name    : Formalism.FourierDecayAlt.P.Jx7.memP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:54.876264+00:00
-- url     : https://prove2.me/theorems/dd8de472-62b9-4f37-82c7-5c89cff60c71
-- title:
--   Jx7: mem P
-- statement:
--   The Jx7 construction uses the mem P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L177-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L177-L180

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

theorem Formalism.FourierDecayAlt.P.Jx7.memP (b : ℕ) (hb : 1 ≤ b) (hbs : b ≤ G.r + 1) :
    (∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')) ∈
      G.thrSet C de de' T T' l := by sorry
