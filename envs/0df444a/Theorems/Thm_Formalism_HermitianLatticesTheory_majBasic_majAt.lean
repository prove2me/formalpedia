-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majBasic_majAt
-- name    : Formalism.HermitianLatticesTheory.majBasic_majAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:37.690857+00:00
-- url     : https://prove2.me/theorems/a2cbc20b-7608-48a3-9090-b43ccb82387e
-- title:
--   Hermitian Lattices Theory: maj Basic maj At
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Basic maj At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajBasic.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajBasic.lean#L16-L21

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HermitianLatticesTheory.majBasic_majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    majAt b X v x y = star (vecAt b v x) ⬝ᵥ ((((X v)⁻¹)ᴴ * (X v)⁻¹) *ᵥ vecAt b v y) := by sorry
