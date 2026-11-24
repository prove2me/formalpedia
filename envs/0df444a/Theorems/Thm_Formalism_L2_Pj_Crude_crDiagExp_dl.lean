-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crDiagExp_dl
-- name    : Formalism.L2.Pj.Crude.crDiagExp_dl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:10.260997+00:00
-- url     : https://prove2.me/theorems/385cb4d6-edda-4cc7-8560-4a2c5ed44266
-- title:
--   Crude: cr Diag Exp dl
-- statement:
--   The Crude construction uses the cr Diag Exp dl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L373-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L373-L380

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

theorem Formalism.L2.Pj.Crude.crDiagExp_dl (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (p : Σ σ : T, Fin (r σ)) :
    diagExp r n β a (crDl β p) = a p.1 p.2 := by sorry
