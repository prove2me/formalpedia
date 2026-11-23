-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crPderiv_supported
-- name    : Formalism.L2.Pj.Crude.crPderiv_supported
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:12.532856+00:00
-- url     : https://prove2.me/theorems/98ff0647-07d1-44a1-9270-5fa9c81c2014
-- title:
--   Crude: cr Pderiv supported
-- statement:
--   The Crude construction uses the cr Pderiv supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L65-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L65-L86

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

theorem Formalism.L2.Pj.Crude.crPderiv_supported {R : Type} [CommRing R] {s : Set (Letter T r n)} (i : Letter T r n)
    {p : MvPolynomial (Letter T r n) R} (hp : p ∈ supported R s) : pderiv i p ∈ supported R s := by sorry
