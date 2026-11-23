-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_ls_mem_Icc
-- name    : Formalism.FourierDecayAlt.P.TA1.ls_mem_Icc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:10.421813+00:00
-- url     : https://prove2.me/theorems/9c461b80-7f5f-4089-892f-b00b1141df6f
-- title:
--   TA1: ls mem Icc
-- statement:
--   The TA1 construction uses the ls mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L86-L90

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

theorem Formalism.FourierDecayAlt.P.TA1.ls_mem_Icc (Sg : ℕ → ℕ → Finset E) (i : ℕ) (hi : 1 ≤ i) (p : Pt E) (hp : p ∈ PT Sg i) :
    ls p ∈ Icc 1 i := by sorry
