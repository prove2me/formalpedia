-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_locP
-- name    : Formalism.HermitianLatticesTheory.exampleZ_mem_locP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:01.489046+00:00
-- url     : https://prove2.me/theorems/b6ace3e7-47e5-4a7b-abde-e46d7a532873
-- title:
--   Hermitian Lattices Theory: example Z mem loc P
-- statement:
--   The Hermitian Lattices Theory construction uses the example Z mem loc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L21-L25

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

theorem Formalism.HermitianLatticesTheory.exampleZ_mem_locP (p : Ideal ℤ) [p.IsPrime] (L : Submodule ℤ ℚ) (x : ℚ) :
    x ∈ localization₂ p L ↔ ∃ s : ℤ, s ∉ p ∧ (s : ℚ) * x ∈ L := by sorry
