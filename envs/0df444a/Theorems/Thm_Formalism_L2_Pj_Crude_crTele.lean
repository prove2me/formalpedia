-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crTele
-- name    : Formalism.L2.Pj.Crude.crTele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:59.552167+00:00
-- url     : https://prove2.me/theorems/6995ca88-793f-46f6-b663-931c3fbf2e60
-- title:
--   Crude: cr Tele
-- statement:
--   The Crude construction uses the cr Tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L233-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L233-L261

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}

theorem Formalism.L2.Pj.Crude.crTele (f : ℕ → ℕ) (R : ℕ) (hf : ∀ j, j < R → f (j + 1) ≤ f j) (hR : f R = 0) :
    ∀ d i, i + d = R → ∑ j ∈ Finset.range R, (if i ≤ j then f j - f (j + 1) else 0) = f i := by sorry
