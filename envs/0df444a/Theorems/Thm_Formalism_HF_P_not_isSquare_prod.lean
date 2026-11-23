-- Prove2me | Theorems.Thm_Formalism_HF_P_not_isSquare_prod
-- name    : Formalism.HF.P.not_isSquare_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:40.882909+00:00
-- url     : https://prove2.me/theorems/598aa523-5e00-47e4-a8f0-ba15b09af80e
-- title:
--   P: not is Square prod
-- statement:
--   The P construction uses the not is Square prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/MQDiscr.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/MQDiscr.lean#L11-L43

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

theorem Formalism.HF.P.not_isSquare_prod {k : ℕ} (q : Fin k → ℕ) (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (S : Finset (Fin k)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (((fun i => -(q i : ℤ)) i : ℤ) : ℚ)) := by sorry
