-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_one
-- name    : Formalism.L2.Pj.Crude.crIsMono_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:10.873581+00:00
-- url     : https://prove2.me/theorems/2ce72b7a-15db-43d4-a53b-81fbbc8cd356
-- title:
--   Crude: cr Is Mono one
-- statement:
--   The Crude construction uses the cr Is Mono one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L460-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L460-L462

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

theorem Formalism.L2.Pj.Crude.crIsMono_one {R : Type} [CommRing R] : crIsMono (1 : MvPolynomial (Letter T r n) R) := by sorry
