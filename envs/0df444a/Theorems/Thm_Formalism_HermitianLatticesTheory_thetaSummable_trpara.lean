-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_trpara
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_trpara
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:45.146259+00:00
-- url     : https://prove2.me/theorems/1ae09994-7764-44fd-b2ce-b159d407c5e0
-- title:
--   Hermitian Lattices Theory: theta Summable trpara
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable trpara property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L62-L68

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLatticesTheory.thetaSummable_trpara (h : V →ₗ⋆[K] V →ₗ[K] K) (u v : V) :
    Algebra.trace ℚ K (h (u + v) (u + v)) + Algebra.trace ℚ K (h (u - v) (u - v)) =
      2 * Algebra.trace ℚ K (h u u) + 2 * Algebra.trace ℚ K (h v v) := by sorry
