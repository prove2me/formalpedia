-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_locS
-- name    : Formalism.HermitianLatticesTheory.isomAct_mem_locS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:23.473937+00:00
-- url     : https://prove2.me/theorems/73079cd8-fda2-47ef-9c48-f370d499b3ee
-- title:
--   Hermitian Lattices Theory: isom Act mem loc S
-- statement:
--   The Hermitian Lattices Theory construction uses the isom Act mem loc S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L47-L48

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
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
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.isomAct_mem_locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R)
    (L : Submodule R W) (x : W) : x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := by sorry
