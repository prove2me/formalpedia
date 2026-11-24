-- Prove2me | Theorems.Thm_Formalism_L2_Pj_TranscendenceDegreeLemmas_trdeg_residueField_genericPoint
-- name    : Formalism.L2.Pj.TranscendenceDegreeLemmas.trdeg_residueField_genericPoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:28.910667+00:00
-- url     : https://prove2.me/theorems/1018eb7d-b938-47c5-beca-f336568e6106
-- title:
--   Transcendence Degree Lemmas: trdeg residue Field generic Point
-- statement:
--   The Transcendence Degree Lemmas construction uses the trdeg residue Field generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/KapTrdegPfB.lean#L32-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/KapTrdegPfB.lean#L32-L71

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.TranscendenceDegreeLemmas
open AlgebraicGeometry CategoryTheory

theorem Formalism.L2.Pj.TranscendenceDegreeLemmas.trdeg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    Algebra.trdeg K (X.residueField hZ.1.genericPoint) = n := by sorry
