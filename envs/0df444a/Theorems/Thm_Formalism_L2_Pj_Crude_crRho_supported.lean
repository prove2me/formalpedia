-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crRho_supported
-- name    : Formalism.L2.Pj.Crude.crRho_supported
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:04.723129+00:00
-- url     : https://prove2.me/theorems/48c3f180-b7e4-4f6f-a8f2-008760217381
-- title:
--   Crude: cr Rho supported
-- statement:
--   The Crude construction uses the cr Rho supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L423-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L423-L435

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

theorem Formalism.L2.Pj.Crude.crRho_supported (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (p : MvPolynomial (Letter T r n) R) : crRho R β p ∈ supported R (crDiag β) := by sorry
