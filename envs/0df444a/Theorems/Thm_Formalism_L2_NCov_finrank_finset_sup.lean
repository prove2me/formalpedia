-- Prove2me | Theorems.Thm_Formalism_L2_NCov_finrank_finset_sup
-- name    : Formalism.L2.NCov.finrank_finset_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:15.088826+00:00
-- url     : https://prove2.me/theorems/a21004a0-76a7-4ee4-b91e-5b81b07cc78c
-- title:
--   NCov: finrank finset sup
-- statement:
--   The NCov construction uses the finrank finset sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L61-L73

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

theorem Formalism.L2.NCov.finrank_finset_sup [FiniteDimensional K V] {ι : Type*} {p : ι → Submodule K V} (hp : iSupIndep p)
    (s : Finset ι) : finrank K ↥(s.sup p) = ∑ i ∈ s, finrank K ↥(p i) := by sorry
