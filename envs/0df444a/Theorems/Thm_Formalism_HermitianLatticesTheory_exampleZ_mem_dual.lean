-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_dual
-- name    : Formalism.HermitianLatticesTheory.exampleZ_mem_dual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:23.236631+00:00
-- url     : https://prove2.me/theorems/813f0734-09af-4c96-b249-d2cd3249ac50
-- title:
--   Hermitian Lattices Theory: example Z mem dual
-- statement:
--   The Hermitian Lattices Theory construction uses the example Z mem dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L16-L19

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory

theorem Formalism.HermitianLatticesTheory.exampleZ_mem_dual (h : ℚ →ₗ⋆[ℚ] ℚ →ₗ[ℚ] ℚ) (L : Submodule ℤ ℚ) (x : ℚ) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule ℤ ℚ) := by sorry
