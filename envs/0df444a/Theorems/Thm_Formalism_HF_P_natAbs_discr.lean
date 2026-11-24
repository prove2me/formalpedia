-- Prove2me | Theorems.Thm_Formalism_HF_P_natAbs_discr
-- name    : Formalism.HF.P.natAbs_discr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:23.364659+00:00
-- url     : https://prove2.me/theorems/c4ae0a72-35a3-4e9a-a8c0-f9943cfb54a8
-- title:
--   P: nat Abs discr
-- statement:
--   The P construction uses the nat Abs discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/MQDiscr.lean#L70-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/MQDiscr.lean#L70-L151

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

theorem Formalism.HF.P.natAbs_discr (hQ : QuadDiscr) : ∀ (m : ℕ) (q : Fin (m + 1) → ℕ),
    (∀ i, (q i).Prime ∧ q i % 4 = 3) → Function.Injective q →
    ∀ (E : Type) [Field E] [NumberField E] (α : Fin (m + 1) → E),
      IsMQ (fun i => -(q i : ℤ)) α → (discr E).natAbs = ∏ i, q i ^ (2 ^ m) := by sorry
