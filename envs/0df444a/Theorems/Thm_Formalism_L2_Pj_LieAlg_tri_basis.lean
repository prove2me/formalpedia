-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LieAlg_tri_basis
-- name    : Formalism.L2.Pj.LieAlg.tri_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:08.310569+00:00
-- url     : https://prove2.me/theorems/0f6fa9af-7acb-48fa-9aa4-e038562abe80
-- title:
--   Lie Alg: tri basis
-- statement:
--   The Lie Alg construction uses the tri basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L261-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L261-L283

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

theorem Formalism.L2.Pj.LieAlg.tri_basis {n m : ℕ} (P : (Fin n → K) → Prop) (v : Fin m → (Fin n → K))
    (hb : ∀ w, P w → ∃! cf : Fin m → K, w = ∑ i, cf i • v i) (C : Fin m → Fin m → K)
    (hCz : ∀ i j, i < j → C i j = 0) (hCd : ∀ i, C i i ≠ 0) :
    ∀ w, P w → ∃! d : Fin m → K, w = ∑ i, d i • ∑ j, C i j • v j := by sorry
