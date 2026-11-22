-- Prove2me | Theorems.Thm_Formalism_L2_NCov_eq_of_le_maxGen
-- name    : Formalism.L2.NCov.eq_of_le_maxGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:30.790017+00:00
-- url     : https://prove2.me/theorems/e3dfdaac-38b7-4c3e-88dd-3b5dc7040b16
-- title:
--   NCov: eq of le max Gen
-- statement:
--   The NCov construction uses the eq of le max Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L56-L59

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
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.NCov.eq_of_le_maxGen {W : Submodule K V} (hW : W ≠ ⊥) {f : End K V} {a b : K}
    (ha : W ≤ f.maxGenEigenspace a) (hb : W ≤ f.maxGenEigenspace b) : a = b := by sorry
