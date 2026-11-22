-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_smul
-- name    : Formalism.HermitianLatticesTheory.isomAct_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:18.63124+00:00
-- url     : https://prove2.me/theorems/0cb2aac5-77a4-4599-bc09-91e668279b59
-- title:
--   Hermitian Lattices Theory: isom Act smul
-- statement:
--   The Hermitian Lattices Theory construction uses the isom Act smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IsomAct.lean#L25-L26

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

theorem Formalism.HermitianLatticesTheory.isomAct_smul (g : V ≃ₗ[K] V) (s : R) (x : V) : g (s • x) = s • g x := by sorry
