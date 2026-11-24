-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crP_isWeightedHomogeneous_crW
-- name    : Formalism.L2.Pj.Crude.crP_isWeightedHomogeneous_crW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:40.939798+00:00
-- url     : https://prove2.me/theorems/dcc9adcd-d12e-4906-afc8-07334e27a682
-- title:
--   Crude: cr P is Weighted Homogeneous cr W
-- statement:
--   The Crude construction uses the cr P is Weighted Homogeneous cr W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L286-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L286-L311

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

theorem Formalism.L2.Pj.Crude.crP_isWeightedHomogeneous_crW (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (ha : Dom r a) (σ : T) (i : Fin (r σ)) :
    IsWeightedHomogeneous (crW (r := r) (n := n) σ i.val) (crP r n R β a) (a σ i) := by sorry
