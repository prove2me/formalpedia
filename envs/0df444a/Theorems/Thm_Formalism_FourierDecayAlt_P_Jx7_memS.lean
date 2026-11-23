-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_memS
-- name    : Formalism.FourierDecayAlt.P.Jx7.memS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:59.681801+00:00
-- url     : https://prove2.me/theorems/73c210b3-c146-4f9f-8325-3e680f414b40
-- title:
--   Jx7: mem S
-- statement:
--   The Jx7 construction uses the mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L156-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L156-L175

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

theorem Formalism.FourierDecayAlt.P.Jx7.memS (hX : XIsLamOne) (b s : ℕ) (hb : 1 ≤ b) (hs : 1 ≤ s) (hbs : b + s ≤ G.r + 2) :
    (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)) ∈
      G.thrSet C de de' T T' l := by sorry
