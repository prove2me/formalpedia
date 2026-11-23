-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_expand
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:12.619184+00:00
-- url     : https://prove2.me/theorems/5f3b63d4-ae03-470b-86d0-7a9ab7797161
-- title:
--   Hermitian Lattices Theory: theta Summable expand
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L89-L96

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

theorem Formalism.HermitianLatticesTheory.thetaSummable_expand (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} [Fintype ι] (e : ι → V) (c : ι → ℤ) :
    Algebra.trace ℚ K (h (∑ i, c i • e i) (∑ i, c i • e i)) =
      ∑ i, ∑ j, (c i : ℚ) * (c j : ℚ) * Algebra.trace ℚ K (h (e i) (e j)) := by sorry
