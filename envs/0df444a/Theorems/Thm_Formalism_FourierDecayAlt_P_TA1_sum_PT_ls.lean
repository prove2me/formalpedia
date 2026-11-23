-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_sum_PT_ls
-- name    : Formalism.FourierDecayAlt.P.TA1.sum_PT_ls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:59.798652+00:00
-- url     : https://prove2.me/theorems/0545ffd3-a711-4a1c-a3bb-d7f0870ba4b5
-- title:
--   TA1: sum PT ls
-- statement:
--   The TA1 construction uses the sum PT ls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L108-L117

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} [DecidableEq E]

theorem Formalism.FourierDecayAlt.P.TA1.sum_PT_ls {M : Type} [AddCommMonoid M] (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s)
    (hsi : s ≤ i) (F : Pt E → M) :
    ∑ p ∈ PT Sg i, (if ls p = s then F p else 0) =
      ∑ t ∈ Sg i s, ∑ h ∈ PT Sg (i - s), F (Formalism.FourierDecayAlt.TA.ext h s t) := by sorry
