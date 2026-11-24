-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crDl_inj
-- name    : Formalism.L2.Pj.Crude.crDl_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.737412+00:00
-- url     : https://prove2.me/theorems/30156323-a6ba-401d-b6dc-6855c98842a6
-- title:
--   Crude: cr Dl inj
-- statement:
--   The Crude construction uses the cr Dl inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L360-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L360-L366

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

theorem Formalism.L2.Pj.Crude.crDl_inj (β : (Σ σ : T, Fin (r σ)) → Fin n) : Function.Injective (crDl (r := r) (n := n) β) := by sorry
