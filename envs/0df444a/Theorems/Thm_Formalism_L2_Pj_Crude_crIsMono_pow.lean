-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_pow
-- name    : Formalism.L2.Pj.Crude.crIsMono_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.837895+00:00
-- url     : https://prove2.me/theorems/374e2ae1-5651-47ae-b061-64e33267c44d
-- title:
--   Crude: cr Is Mono pow
-- statement:
--   The Crude construction uses the cr Is Mono pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L464-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L464-L472

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

theorem Formalism.L2.Pj.Crude.crIsMono_pow {R : Type} [CommRing R] {p : MvPolynomial (Letter T r n) R} (hp : crIsMono p)
    (e : ℕ) : crIsMono (p ^ e) := by sorry
