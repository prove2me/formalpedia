-- Prove2me | Theorems.Thm_Formalism_L2_NCov_iSupIndep_alt
-- name    : Formalism.L2.NCov.iSupIndep_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:45.564799+00:00
-- url     : https://prove2.me/theorems/506fe239-694b-4a0e-813c-881401ba3b7e
-- title:
--   NCov: i Sup Indep alt
-- statement:
--   The NCov construction uses the i Sup Indep alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L182-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L182-L184

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

theorem Formalism.L2.NCov.iSupIndep_alt (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) : iSupIndep (W (Algebra.adjoin O S)) := by sorry
