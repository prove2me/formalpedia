-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crRho_monomial
-- name    : Formalism.L2.Pj.Crude.crRho_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:11.240589+00:00
-- url     : https://prove2.me/theorems/af7b182e-66db-42e1-9d5d-7ee221c82a21
-- title:
--   Crude: cr Rho monomial
-- statement:
--   The Crude construction uses the cr Rho monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L393-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L393-L407

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

theorem Formalism.L2.Pj.Crude.crRho_monomial (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (u : Letter T r n →₀ ℕ) (c : R) :
    crRho R β (monomial u c) =
      if (∀ ℓ ∈ u.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩) then monomial u c else 0 := by sorry
