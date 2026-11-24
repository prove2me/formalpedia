-- Prove2me | Theorems.Thm_Formalism_L2_Pj_iwasawa
-- name    : Formalism.L2.Pj.iwasawa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:48.223116+00:00
-- url     : https://prove2.me/theorems/8d554672-63b7-4778-925f-90c7a5808296
-- title:
--   Pj: iwasawa
-- statement:
--   The Pj construction uses the iwasawa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExistsOfValILeOne.lean#L85-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExistsOfValILeOne.lean#L85-L138

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

theorem Formalism.L2.Pj.iwasawa : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U
  := by sorry
