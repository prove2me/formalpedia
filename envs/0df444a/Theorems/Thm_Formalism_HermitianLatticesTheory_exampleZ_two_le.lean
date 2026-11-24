-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_two_le
-- name    : Formalism.HermitianLatticesTheory.exampleZ_two_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:00.009189+00:00
-- url     : https://prove2.me/theorems/ed0036c5-219d-4f38-ac09-b0e6c45df427
-- title:
--   Hermitian Lattices Theory: example Z two le
-- statement:
--   The Hermitian Lattices Theory construction uses the example Z two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L41-L43

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

theorem Formalism.HermitianLatticesTheory.exampleZ_two_le : Submodule.span ℤ {(2 : ℚ)} ≤ (1 : Submodule ℤ ℚ) := by sorry
