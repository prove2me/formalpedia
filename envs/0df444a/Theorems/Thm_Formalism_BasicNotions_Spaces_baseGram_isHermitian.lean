-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Spaces_baseGram_isHermitian
-- name    : Formalism.BasicNotions.Spaces.baseGram_isHermitian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:27.634868+00:00
-- url     : https://prove2.me/theorems/a94d6b3b-3bae-4cd8-a422-171dd7ac8aca
-- title:
--   Spaces: base Gram is Hermitian
-- statement:
--   The Spaces construction uses the base Gram is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataLevel.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataLevel.lean#L77-L82

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
open Formalism.BasicNotions.Spaces
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem Formalism.BasicNotions.Spaces.baseGram_isHermitian : IsHerm (sp.cm.sig : E →+* E) sp.gram0 := by sorry
