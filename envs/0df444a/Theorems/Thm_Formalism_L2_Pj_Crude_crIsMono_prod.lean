-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_prod
-- name    : Formalism.L2.Pj.Crude.crIsMono_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.644606+00:00
-- url     : https://prove2.me/theorems/d9352450-4304-4296-b385-03d1127891cb
-- title:
--   Crude: cr Is Mono prod
-- statement:
--   The Crude construction uses the cr Is Mono prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L474-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L474-L476

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

theorem Formalism.L2.Pj.Crude.crIsMono_prod {R : Type} [CommRing R] {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Letter T r n) R) (h : ∀ i ∈ s, crIsMono (f i)) : crIsMono (∏ i ∈ s, f i) := by sorry
