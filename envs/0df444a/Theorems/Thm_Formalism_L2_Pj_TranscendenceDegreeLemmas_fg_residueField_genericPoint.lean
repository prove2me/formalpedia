-- Prove2me | Theorems.Thm_Formalism_L2_Pj_TranscendenceDegreeLemmas_fg_residueField_genericPoint
-- name    : Formalism.L2.Pj.TranscendenceDegreeLemmas.fg_residueField_genericPoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:28.279214+00:00
-- url     : https://prove2.me/theorems/a5551da9-c1bf-4300-b375-384d9de473be
-- title:
--   Transcendence Degree Lemmas: fg residue Field generic Point
-- statement:
--   The Transcendence Degree Lemmas construction uses the fg residue Field generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/KapTrdegPfB.lean#L73-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/KapTrdegPfB.lean#L73-L118

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

theorem Formalism.L2.Pj.TranscendenceDegreeLemmas.fg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    (⊤ : IntermediateField K (X.residueField hZ.1.genericPoint)).FG := by sorry
