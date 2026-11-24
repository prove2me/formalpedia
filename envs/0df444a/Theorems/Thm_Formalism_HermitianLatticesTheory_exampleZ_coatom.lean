-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_coatom
-- name    : Formalism.HermitianLatticesTheory.exampleZ_coatom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:07.754797+00:00
-- url     : https://prove2.me/theorems/654524e9-6b6a-4c59-8857-dbca11769bc3
-- title:
--   Hermitian Lattices Theory: example Z coatom
-- statement:
--   The Hermitian Lattices Theory construction uses the example Z coatom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L48-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L48-L101

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

theorem Formalism.HermitianLatticesTheory.exampleZ_coatom (p : Ideal ℤ) [p.IsPrime] (hp : p = Ideal.span {2}) :
    IsCoatom ((localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap (localization₂ p (1 : Submodule ℤ ℚ)).subtype) := by sorry
