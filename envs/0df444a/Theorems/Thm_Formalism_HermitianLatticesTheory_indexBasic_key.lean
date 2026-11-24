-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_key
-- name    : Formalism.HermitianLatticesTheory.indexBasic_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:44.403934+00:00
-- url     : https://prove2.me/theorems/57c03db7-de87-42ea-b852-352f59ab644a
-- title:
--   Hermitian Lattices Theory: index Basic key
-- statement:
--   The Hermitian Lattices Theory construction uses the index Basic key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IndexBasic.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IndexBasic.lean#L16-L31

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem Formalism.HermitianLatticesTheory.indexBasic_key [IsNoetherianRing R] [Ring.KrullDimLE 1 R] {d : R}
    (hd : d ∈ nonZeroDivisors R) (s : R) :
    ∃ n : ℕ, ∃ t : R, ∃ u : R, s ^ n - s ^ (n + 1) * t = d * u := by sorry
