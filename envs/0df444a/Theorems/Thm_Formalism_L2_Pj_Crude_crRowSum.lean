-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crRowSum
-- name    : Formalism.L2.Pj.Crude.crRowSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:25.020507+00:00
-- url     : https://prove2.me/theorems/9024c015-4554-487d-ad3e-2e5dd1269ca8
-- title:
--   Crude: cr Row Sum
-- statement:
--   The Crude construction uses the cr Row Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L224-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L224-L231

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

theorem Formalism.L2.Pj.Crude.crRowSum (τ σ : T) (m i0 : ℕ) :
    (∑ j : Fin m, if τ = σ ∧ (j : ℕ) = i0 then 1 else 0) = if τ = σ ∧ i0 < m then 1 else 0 := by sorry
