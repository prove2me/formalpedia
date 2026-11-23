-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_mul
-- name    : Formalism.HermitianLatticesTheory.genusBasic_gmap_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.019106+00:00
-- url     : https://prove2.me/theorems/cf9e694e-422b-44ed-9a89-45ffb50f07ab
-- title:
--   Hermitian Lattices Theory: genus Basic gmap mul
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Basic gmap mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusBasic.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusBasic.lean#L24-L28

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
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
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.genusBasic_gmap_mul (g₁ g₂ : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (g₂ * g₁) L = gmap g₂ (gmap g₁ L) := by sorry
