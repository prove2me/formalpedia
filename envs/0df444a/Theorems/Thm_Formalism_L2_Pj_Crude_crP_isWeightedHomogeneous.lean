-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crP_isWeightedHomogeneous
-- name    : Formalism.L2.Pj.Crude.crP_isWeightedHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:56.36237+00:00
-- url     : https://prove2.me/theorems/43ae1a35-a9a0-4c3e-acfd-33a2a1121912
-- title:
--   Crude: cr P is Weighted Homogeneous
-- statement:
--   The Crude construction uses the cr P is Weighted Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L216-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L216-L222

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

theorem Formalism.L2.Pj.Crude.crP_isWeightedHomogeneous (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (w : Letter T r n → ℕ) (D : ∀ τ : T, Fin (r τ) → ℕ)
    (hD : ∀ τ kk, IsWeightedHomogeneous w (crMinor r n R β τ kk).det (D τ kk)) :
    IsWeightedHomogeneous w (crP r n R β a) (∑ τ, ∑ kk, crExp r a τ kk • D τ kk) := by sorry
