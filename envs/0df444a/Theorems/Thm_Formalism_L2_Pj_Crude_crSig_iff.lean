-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crSig_iff
-- name    : Formalism.L2.Pj.Crude.crSig_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:24.769305+00:00
-- url     : https://prove2.me/theorems/a3548f90-5a12-4cd2-90e2-09dd5bcabdc6
-- title:
--   Crude: cr Sig iff
-- statement:
--   The Crude construction uses the cr Sig iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L130-L136

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

theorem Formalism.L2.Pj.Crude.crSig_iff {τ : T} {x i : Fin (r τ)} {y : Fin n} :
    (∃ b : Fin n, (⟨τ, x, y⟩ : Letter T r n) = ⟨τ, i, b⟩) ↔ x = i := by sorry
