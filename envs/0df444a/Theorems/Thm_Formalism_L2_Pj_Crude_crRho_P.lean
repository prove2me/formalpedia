-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crRho_P
-- name    : Formalism.L2.Pj.Crude.crRho_P
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:54.291751+00:00
-- url     : https://prove2.me/theorems/bee5c985-9ac5-4f59-8838-5bf07b30e683
-- title:
--   Crude: cr Rho P
-- statement:
--   The Crude construction uses the cr Rho P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L478-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L478-L488

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

theorem Formalism.L2.Pj.Crude.crRho_P (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (hβ : Function.Injective β) : crIsMono (crRho R β (crP r n R β a)) := by sorry
