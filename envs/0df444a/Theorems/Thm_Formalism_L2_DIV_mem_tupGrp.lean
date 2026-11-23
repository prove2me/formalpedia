-- Prove2me | Theorems.Thm_Formalism_L2_DIV_mem_tupGrp
-- name    : Formalism.L2.DIV.mem_tupGrp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:53.080508+00:00
-- url     : https://prove2.me/theorems/2f3037e1-d491-43dc-9e9f-3c81ebbf255e
-- title:
--   DIV: mem tup Grp
-- statement:
--   The DIV construction uses the mem tup Grp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L14-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem Formalism.L2.DIV.mem_tupGrp {S : Set ℕ} (ξ : Chr F E L) : ξ ∈ tupGrp F E L S ↔
    ((ratId F E).range ≤ ξ.ker ∧ (∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker) ∧ IsOfFinOrder ξ) ∧
      (idF F E).range ≤ ξ.ker ∧ (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ¬ GoodPl E S v → inertAt E v ≤ ξ.ker := by sorry
