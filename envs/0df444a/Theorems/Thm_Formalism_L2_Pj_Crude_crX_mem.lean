-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crX_mem
-- name    : Formalism.L2.Pj.Crude.crX_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:32.628798+00:00
-- url     : https://prove2.me/theorems/955b5839-1791-4c66-a92d-c1d730e0aa84
-- title:
--   Crude: cr X mem
-- statement:
--   The Crude construction uses the cr X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L51-L53

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

theorem Formalism.L2.Pj.Crude.crX_mem {R : Type} [CommRing R] {s : Set (Letter T r n)} {ℓ : Letter T r n} (h : ℓ ∈ s) :
    (X ℓ : MvPolynomial (Letter T r n) R) ∈ supported R s := by sorry
