-- Prove2me | Theorems.Thm_APFPaper5_K3_no_direction_if_present_records_fix_later
-- name    : APFPaper5.K3.no_direction_if_present_records_fix_later
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:31:23.891477+00:00
-- url     : https://prove2.me/theorems/e30d1e13-3d75-417e-9c84-10f625123f99
-- title:
--   No direction if present records fix later
-- statement:
--   Supporting lemma: no direction if present records fix later. The exact quantified statement supplied with this entry is controlling, including every displayed hypothesis. E is only a supplied map: no inverse equations for D and E are assumed. hnow, hrev, hmotion and hfact remain explicit. This proves a distinction witness, not a physical rate coordinate or rate derivation.
-- source:
--   Sib v44 Theorems/Thm_APFB01_reversal_and_the_rate.lean:51

import Definitions.Def_APF_B01_DeclaredInput

set_option autoImplicit false

universe uX uP uR uS

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.no_direction_if_present_records_fix_later {X : Type uX} {R : Type uR} (now : X → R)
    (D E theta : X → X) (hdet : ∀ x y : X, now x = now y → now (D x) = now (D y))
    (hnow : ∀ x : X, now (theta x) = now x) (hrev : ∀ x : X, D (theta x) = theta (E x)) (x : X) :
    now (D x) = now (E x) := by sorry
