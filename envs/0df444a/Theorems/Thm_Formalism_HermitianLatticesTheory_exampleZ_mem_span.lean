-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_span
-- name    : Formalism.HermitianLatticesTheory.exampleZ_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:55.323998+00:00
-- url     : https://prove2.me/theorems/78a5f7bc-b5b4-4b82-9fe6-f0b9885c3cab
-- title:
--   Hermitian Lattices Theory: example Z mem span
-- statement:
--   The Hermitian Lattices Theory construction uses the example Z mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L12-L14

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

theorem Formalism.HermitianLatticesTheory.exampleZ_mem_span (c x : ℚ) : x ∈ Submodule.span ℤ {c} ↔ ∃ n : ℤ, (n : ℚ) * c = x := by sorry
