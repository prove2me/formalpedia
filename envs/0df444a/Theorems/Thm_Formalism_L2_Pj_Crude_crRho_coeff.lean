-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crRho_coeff
-- name    : Formalism.L2.Pj.Crude.crRho_coeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:07.508144+00:00
-- url     : https://prove2.me/theorems/b22cd3b0-6b08-4770-aa61-1ad9071b4d16
-- title:
--   Crude: cr Rho coeff
-- statement:
--   The Crude construction uses the cr Rho coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L409-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L409-L421

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

theorem Formalism.L2.Pj.Crude.crRho_coeff (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (p : MvPolynomial (Letter T r n) R) (m : Letter T r n →₀ ℕ)
    (hm : ∀ ℓ ∈ m.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩) : coeff m (crRho R β p) = coeff m p := by sorry
