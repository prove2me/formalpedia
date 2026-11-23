-- Prove2me | Theorems.Thm_Formalism_L2_NCov_chi_alg
-- name    : Formalism.L2.NCov.chi_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:22.889118+00:00
-- url     : https://prove2.me/theorems/d67d933f-2c2d-44ea-af4c-e54332c3d36b
-- title:
--   NCov: chi alg
-- statement:
--   The NCov construction uses the chi alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L143-L147

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [IsLocalRing O]
variable {S : Set (End K V)}

theorem Formalism.L2.NCov.chi_alg {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) (c : O) :
    χ (algebraMap O (Algebra.adjoin O S) c) = algebraMap O K c := by sorry
