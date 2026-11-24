-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_loc_dual
-- name    : Formalism.HermitianLatticesTheory.genusBasic_loc_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:14.843794+00:00
-- url     : https://prove2.me/theorems/a4ffeca9-f39b-4aaa-87a8-39953843e487
-- title:
--   Hermitian Lattices Theory: genus Basic loc dual
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Basic loc dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusBasic.lean#L91-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusBasic.lean#L91-L115

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

theorem Formalism.HermitianLatticesTheory.genusBasic_loc_dual (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (hL : L.FG) (z : V)
    (hz : ∀ v ∈ L, h v z ∈ loc (K := K) p (1 : Submodule R K)) :
    z ∈ loc (K := K) p (dual h L) := by sorry
