-- Prove2me | Theorems.Thm_Bl_FirstLemmaE_goal1
-- name    : Bl.FirstLemmaE.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:10.434802+00:00
-- url     : https://prove2.me/theorems/7f972ea5-b44b-4a32-b234-0aec931c7b0f
-- title:
--   First Lemma E: goal1
-- statement:
--   The First Lemma E construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaE.lean#L5-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaE.lean#L5-L36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaE

theorem Bl.FirstLemmaE.goal1 :
  ∀ {L : Type} [inst : NontriviallyNormedField.{0} L] [IsUltrametricDist.{0} L] {ι : Type} (s : Finset.{0} ι)
  (f g : ι → L) {r : Real},
  LE.le.{0} 0 r →
    (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (f i)) 1) →
      (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (g i)) 1) →
        (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (f i) (g i))) r) →
          LE.le.{0}
            (Norm.norm.{0}
              (HSub.hSub.{0, 0, 0} (Finset.prod.{0, 0} s fun (i : ι) ↦ f i) (Finset.prod.{0, 0} s fun (i : ι) ↦ g i)))
            r := by sorry
