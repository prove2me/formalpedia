-- Prove2me | Theorems.Thm_Formalism_L2_NCov_iSup_eq_sup_filter
-- name    : Formalism.L2.NCov.iSup_eq_sup_filter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:42.65461+00:00
-- url     : https://prove2.me/theorems/3a522802-779a-440a-b502-6b70b76de8bf
-- title:
--   NCov: i Sup eq sup filter
-- statement:
--   The NCov construction uses the i Sup eq sup filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L75-L83

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

theorem Formalism.L2.NCov.iSup_eq_sup_filter {ι : Type*} (p : ι → Submodule K V) (F : Finset ι) (hF : ∀ i, p i ≠ ⊥ → i ∈ F)
    (P : ι → Prop) [DecidablePred P] : (⨆ (i) (_ : P i), p i) = (F.filter P).sup p := by sorry
