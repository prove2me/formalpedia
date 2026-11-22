-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_mem_PT_succ
-- name    : Formalism.FourierDecayAlt.P.TA1.mem_PT_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:34.119817+00:00
-- url     : https://prove2.me/theorems/fc1bb89d-4e41-4408-9b8d-8f6a21f667f6
-- title:
--   TA1: mem PT succ
-- statement:
--   The TA1 construction uses the mem PT succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L77-L84

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

theorem Formalism.FourierDecayAlt.P.TA1.mem_PT_succ (Sg : ℕ → ℕ → Finset E) (n : ℕ) (p : Pt E) :
    p ∈ PT Sg (n + 1) ↔ ∃ m, m < n + 1 ∧ ∃ h ∈ PT Sg m, ∃ t ∈ Sg (n + 1) (n + 1 - m),
      Formalism.FourierDecayAlt.TA.ext h (n + 1 - m) t = p := by sorry
