-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crDiagExp_apply
-- name    : Formalism.L2.Pj.Crude.crDiagExp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:59.127168+00:00
-- url     : https://prove2.me/theorems/f0e7e5e9-7f41-45f4-b2da-05b2a7a43e46
-- title:
--   Crude: cr Diag Exp apply
-- statement:
--   The Crude construction uses the cr Diag Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L368-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L368-L371

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

theorem Formalism.L2.Pj.Crude.crDiagExp_apply (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (ℓ : Letter T r n) :
    diagExp r n β a ℓ = ∑ p, if crDl β p = ℓ then a p.1 p.2 else 0 := by sorry
