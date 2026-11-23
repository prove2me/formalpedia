-- Prove2me | Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_dvd_one
-- name    : Formalism.Q3.CMRootsOfUnity.not_dvd_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:15.943799+00:00
-- url     : https://prove2.me/theorems/9a82f2c4-83b6-48d8-b6a2-902c21b140d2
-- title:
--   CMRoots Of Unity: not dvd one
-- statement:
--   The CMRoots Of Unity construction uses the not dvd one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L47-L50

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}

theorem Formalism.Q3.CMRootsOfUnity.not_dvd_one (hq : Hyp3 q) (i : Fin 3) : ¬ (q i : ℤ) ∣ 1 := by sorry
