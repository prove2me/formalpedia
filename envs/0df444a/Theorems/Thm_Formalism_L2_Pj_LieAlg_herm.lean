-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LieAlg_herm
-- name    : Formalism.L2.Pj.LieAlg.herm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.771814+00:00
-- url     : https://prove2.me/theorems/5efecc5d-fba2-40f5-ba9d-d7aeb2e1f70c
-- title:
--   Lie Alg: herm
-- statement:
--   The Lie Alg construction uses the herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L71-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L71-L166

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem Formalism.L2.Pj.LieAlg.herm (m : ℕ) (Λ : Submodule V (Fin m → K)) (hfg : Λ.FG)
    (hne : ∀ i : Fin m, ∃ α ∈ Λ, (∀ j, i < j → α j = 0) ∧ α i ≠ 0) :
    ∃ β : Fin m → (Fin m → K), (∀ i, β i ∈ Λ) ∧ (∀ i j, i < j → β i j = 0) ∧ (∀ i, β i i ≠ 0) ∧
      ∀ α ∈ Λ, ∃! r : Fin m → V, α = ∑ i, r i • β i := by sorry
