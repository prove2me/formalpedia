-- Prove2me | Theorems.Thm_Bl_FirstLemmaA_goal1
-- name    : Bl.FirstLemmaA.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:32.38299+00:00
-- url     : https://prove2.me/theorems/3bf097fe-7e88-4b9b-a3bc-ac274a551129
-- title:
--   First Lemma A: goal1
-- statement:
--   The First Lemma A construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaA.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaA.lean#L7-L31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.FirstLemmaA

theorem Bl.FirstLemmaA.goal1 :
  ∀ {B : Type u_1} [inst : CommRing.{u_1} B] {ι : Type u_2} (s : Finset.{u_2} ι) (v : ι → Polynomial.{u_1} B)
  (d : ι → Nat),
  (∀ (i : ι), LE.le.{0} (Polynomial.natDegree.{u_1} (v i)) 1) →
    And
      (LE.le.{0}
        (Polynomial.natDegree.{u_1} (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (v i) (d i)))
        (Finset.sum.{u_2, 0} s fun (i : ι) ↦ d i))
      (Eq.{u_1 + 1}
        (Polynomial.coeff.{u_1} (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (v i) (d i))
          (Finset.sum.{u_2, 0} s fun (i : ι) ↦ d i))
        (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (Polynomial.coeff.{u_1} (v i) 1) (d i))) := by sorry
