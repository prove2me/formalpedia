-- Prove2me | Theorems.Thm_Bl_FirstBlockLemmaA_goal1
-- name    : Bl.FirstBlockLemmaA.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:50.446003+00:00
-- url     : https://prove2.me/theorems/52ac19ef-c1c7-4f6e-bee1-00bd86054fcb
-- title:
--   First Block Lemma A: goal1
-- statement:
--   The First Block Lemma A construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaA/Imports.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaA/Imports.lean#L7-L23

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.FirstBlockLemmaA

theorem Bl.FirstBlockLemmaA.goal1 :
  ∀ {k : Type u_1} [inst : Field.{u_1} k] {σ : Type u_2} [Fintype.{u_2} σ] (H : MvPolynomial.{u_2, u_1} σ k) (d : Nat),
  (∀ (m : Finsupp.{u_2, 0} σ Nat),
      Membership.mem.{u_2, u_2} (MvPolynomial.support.{u_1, u_2} H) m →
        Eq.{1} (DFunLike.coe.{max 1 (u_2 + 1), max 1 (u_2 + 1), 1} Finsupp.degree.{u_2, 0} m) d) →
    ∀ (c : k) (v : σ → k),
      Eq.{u_1 + 1}
        (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1), u_1 + 1}
          (MvPolynomial.eval.{u_1, u_2} (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} c v)) H)
        (HMul.hMul.{u_1, u_1, u_1} (HPow.hPow.{u_1, 0, u_1} c d)
          (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1), u_1 + 1} (MvPolynomial.eval.{u_1, u_2} v) H)) := by sorry
