-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crW_weight
-- name    : Formalism.L2.Pj.Crude.crW_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:25.307911+00:00
-- url     : https://prove2.me/theorems/0788baa7-861d-4a29-97ac-db39b67a3abc
-- title:
--   Crude: cr W weight
-- statement:
--   The Crude construction uses the cr W weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L313-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L313-L342

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

theorem Formalism.L2.Pj.Crude.crW_weight (m : Letter T r n →₀ ℕ) (σ : T) (i : Fin (r σ)) :
    Finsupp.weight (crW (r := r) (n := n) σ i.val) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by sorry
