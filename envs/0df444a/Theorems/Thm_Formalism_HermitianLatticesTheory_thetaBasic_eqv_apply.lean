-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaBasic_eqv_apply
-- name    : Formalism.HermitianLatticesTheory.thetaBasic_eqv_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:11.546794+00:00
-- url     : https://prove2.me/theorems/b6249fee-a934-4026-8364-e4c9d9c53bb6
-- title:
--   Hermitian Lattices Theory: theta Basic eqv apply
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Basic eqv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaBasic.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaBasic.lean#L29-L33

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.K
noncomputable section
open Formalism Formalism.HermitianLatticesTheory

theorem Formalism.HermitianLatticesTheory.thetaBasic_eqv_apply {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) (x : L) :
    ((thetaBasic_eqv g L x : gmap g L) : V) = g x := by sorry
