-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_gmap_symm
-- name    : Formalism.HermitianLatticesTheory.isomAct_gmap_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:46.402341+00:00
-- url     : https://prove2.me/theorems/76c6dca2-ead2-4b5d-8e74-da8749f702a1
-- title:
--   Hermitian Lattices Theory: isom Act gmap symm
-- statement:
--   The Hermitian Lattices Theory construction uses the isom Act gmap symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L28-L31

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

theorem Formalism.HermitianLatticesTheory.isomAct_gmap_symm (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g.symm (gmap g L) = L := by sorry
