-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crMinor_hom
-- name    : Formalism.L2.Pj.Crude.crMinor_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:42.68773+00:00
-- url     : https://prove2.me/theorems/6b1efe16-93ba-49a7-bb9a-cefed7c84753
-- title:
--   Crude: cr Minor hom
-- statement:
--   The Crude construction uses the cr Minor hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L203-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L203-L214

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

theorem Formalism.L2.Pj.Crude.crMinor_hom (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (τ : T) (kk : Fin (r τ))
    (w : Letter T r n → ℕ) (D : ℕ)
    (hw : ∀ π : Equiv.Perm (Fin (kk.val + 1)),
      ∑ j, w ⟨τ, Fin.castLE kk.isLt (π j), β ⟨τ, Fin.castLE kk.isLt j⟩⟩ = D) :
    IsWeightedHomogeneous w (crMinor r n R β τ kk).det D := by sorry
