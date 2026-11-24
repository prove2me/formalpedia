-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crRho_minor
-- name    : Formalism.L2.Pj.Crude.crRho_minor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:55.687927+00:00
-- url     : https://prove2.me/theorems/e339df6a-4bfa-42f5-9442-c86a2899b772
-- title:
--   Crude: cr Rho minor
-- statement:
--   The Crude construction uses the cr Rho minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L437-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L437-L449

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

theorem Formalism.L2.Pj.Crude.crRho_minor (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (hβ : Function.Injective β) (τ : T) (kk : Fin (r τ)) :
    (crRho R β).mapMatrix (crMinor r n R β τ kk) =
      Matrix.diagonal (fun q => X ⟨τ, Fin.castLE kk.isLt q, β ⟨τ, Fin.castLE kk.isLt q⟩⟩) := by sorry
