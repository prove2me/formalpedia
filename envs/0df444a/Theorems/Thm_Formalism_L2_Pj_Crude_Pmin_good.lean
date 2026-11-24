-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_Pmin_good
-- name    : Formalism.L2.Pj.Crude.Pmin_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:59.249934+00:00
-- url     : https://prove2.me/theorems/a4d307d8-8e85-41c7-8425-338c13c831e5
-- title:
--   Crude: Pmin good
-- statement:
--   The Crude construction uses the Pmin good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L548-L553
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L548-L553

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
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)

theorem Formalism.L2.Pj.Crude.Pmin_good (m : Letter T r n →₀ ℕ) (hm : m ∈ (MvPolynomial.map (Int.castRingHom k) (Pmin r n β a)).support)
    (ℓ : Letter T r n) (hℓ : m ℓ ≠ 0) : ℓ ∈ GoodL r n β := by sorry
