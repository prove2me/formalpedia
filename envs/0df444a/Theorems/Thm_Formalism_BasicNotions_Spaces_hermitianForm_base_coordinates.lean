-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Spaces_hermitianForm_base_coordinates
-- name    : Formalism.BasicNotions.Spaces.hermitianForm_base_coordinates
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:50.67299+00:00
-- url     : https://prove2.me/theorems/ea421932-2404-4bc6-ac30-8f5b8ef6b8b2
-- title:
--   Spaces: hermitian Form base coordinates
-- statement:
--   The Spaces construction uses the hermitian Form base coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataLevel.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataLevel.lean#L73-L75

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

theorem Formalism.BasicNotions.Spaces.hermitianForm_base_coordinates (x y : (sp.X 0).V) :
    (sp.X 0).hT x y = hform (sp.cm.sig : E →+* E) sp.gram0 (sp.crd0 x) (sp.crd0 y) := by sorry
