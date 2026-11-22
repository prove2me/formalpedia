-- Prove2me | Theorems.Thm_Bl_VolumeRatioCancellation_goal1
-- name    : Bl.VolumeRatioCancellation.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:54.110798+00:00
-- url     : https://prove2.me/theorems/538606de-24ee-438e-8ecb-089d8fa7d4bb
-- title:
--   Volume Ratio Cancellation: goal1
-- statement:
--   The Volume Ratio Cancellation construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/Cancellation/EnnrealVolumeRatioStepCancel.lean#L12-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/Cancellation/EnnrealVolumeRatioStepCancel.lean#L12-L105

import Mathlib
import Definitions.Def_Lemmata_Cancellation_EnnrealVolumeRatioStepCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.VolumeRatioCancellation

theorem Bl.VolumeRatioCancellation.goal1 :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] [inst_1 : IsDedekindDomain.{u_1} R] {K : Type u_2} [inst_2 : Field.{u_2} K]
  [inst_3 : Algebra.{u_1, u_2} R K] [inst_4 : IsFractionRing.{u_1, u_2} R K]
  (T : Finset.{u_1} (IsDedekindDomain.HeightOneSpectrum.{u_1} R))
  (a c : IsDedekindDomain.HeightOneSpectrum.{u_1} R → K),
  (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R), Membership.mem.{u_1, u_1} T p → Ne.{u_2 + 1} (c p) 0) →
    Exists.{u_2 + 1} fun (t : K) ↦
      And
        (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R),
          Membership.mem.{u_1, u_1} T p →
            LE.le.{0}
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p)
                (HSub.hSub.{u_2, u_2, u_2} t (a p)))
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p) (c p)))
        (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R),
          Not (Membership.mem.{u_1, u_1} T p) →
            LE.le.{0}
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p) t) 1) := by sorry
