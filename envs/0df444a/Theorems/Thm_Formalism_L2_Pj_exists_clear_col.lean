-- Prove2me | Theorems.Thm_Formalism_L2_Pj_exists_clear_col
-- name    : Formalism.L2.Pj.exists_clear_col
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:45.848528+00:00
-- url     : https://prove2.me/theorems/74ad38e6-b378-472d-9465-8248439e5def
-- title:
--   Pj: exists clear col
-- statement:
--   The Pj construction uses the exists clear col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExistsOfValILeOne.lean#L26-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExistsOfValILeOne.lean#L26-L83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open Matrix IsDedekindDomain
variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

theorem Formalism.L2.Pj.exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by sorry
