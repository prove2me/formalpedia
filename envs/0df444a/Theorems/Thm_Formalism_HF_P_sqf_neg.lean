-- Prove2me | Theorems.Thm_Formalism_HF_P_sqf_neg
-- name    : Formalism.HF.P.sqf_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:08.523409+00:00
-- url     : https://prove2.me/theorems/6969c0ac-36f5-40ef-9a5d-b862abbc6edd
-- title:
--   P: sqf neg
-- statement:
--   The P construction uses the sqf neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/MQDiscr.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/MQDiscr.lean#L67-L68

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.sqf_neg (p : ℕ) (hp : p.Prime) : Squarefree (-(p : ℤ)) := by sorry
