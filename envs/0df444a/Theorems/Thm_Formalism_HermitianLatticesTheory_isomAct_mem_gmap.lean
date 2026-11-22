-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
-- name    : Formalism.HermitianLatticesTheory.isomAct_mem_gmap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:16.0428+00:00
-- url     : https://prove2.me/theorems/4d6e3e6f-bac0-430c-a6d1-c611c25788d7
-- title:
--   Hermitian Lattices Theory: isom Act mem gmap
-- statement:
--   The Hermitian Lattices Theory construction uses the isom Act mem gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L15-L23

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

theorem Formalism.HermitianLatticesTheory.isomAct_mem_gmap (g : V ≃ₗ[K] V) (L : Submodule R V) (x : V) :
    x ∈ gmap g L ↔ g.symm x ∈ L := by sorry
