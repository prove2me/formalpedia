-- Prove2me | Theorems.Thm_Bl_general_b_fact_upper_bis_goal1
-- name    : Bl.general_b_fact_upper_bis.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:16.815382+00:00
-- url     : https://prove2.me/theorems/5b817665-5e6e-4a93-922d-bc4f6281ba51
-- title:
--   general b fact upper bis: goal1
-- statement:
--   The general b fact upper bis construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperBis/Imports.lean#L5-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperBis/Imports.lean#L5-L164

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperBis_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_bis

theorem Bl.general_b_fact_upper_bis.goal1 :
  ∀ {A K : Type} [inst : CommRing.{0} A] [inst_1 : IsDedekindDomain.{0} A] [inst_2 : Field.{0} K]
  [inst_3 : Algebra.{0, 0} A K] [inst_4 : IsFractionRing.{0, 0} A K] (w : IsDedekindDomain.HeightOneSpectrum.{0} A)
  {V : Type} [inst_5 : AddCommGroup.{0} V] [inst_6 : Module.{0, 0} K V] [inst_7 : Module.{0, 0} A V]
  [IsScalarTower.{0, 0, 0} A K V] {ι : Type} [Fintype.{0} ι] (b : Module.Basis.{0, 0, 0} ι K V) {O Kf Fn : Type}
  [inst_10 : CommRing.{0} O] [inst_11 : Field.{0} Kf] [inst_12 : Algebra.{0, 0} O Kf] [inst_13 : AddCommGroup.{0} Fn]
  [inst_14 : Module.{0, 0} Kf Fn] [inst_15 : Module.{0, 0} O Fn] [IsScalarTower.{0, 0, 0} O Kf Fn]
  (φ : RingHom.{0, 0} K Kf) (cmp : AddMonoidHom.{0, 0} V Fn),
  (∀ (x : K),
      Iff (LE.le.{0} (DFunLike.coe.{1, 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{0, 0} K w) x) 1)
        (Membership.mem.{0, 0} (Set.range.{0, 1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} O Kf)))
          (DFunLike.coe.{1, 1, 1} φ x))) →
    (∀ (a : K) (x : V),
        Eq.{1} (DFunLike.coe.{1, 1, 1} cmp (HSMul.hSMul.{0, 0, 0} a x))
          (HSMul.hSMul.{0, 0, 0} (DFunLike.coe.{1, 1, 1} φ a) (DFunLike.coe.{1, 1, 1} cmp x))) →
      (LinearIndependent.{0, 0, 0} Kf fun (a : ι) ↦ DFunLike.coe.{1, 1, 1} cmp (DFunLike.coe.{1, 1, 1} b a)) →
        ∀ (Lat : Submodule.{0, 0} A V),
          Submodule.FG.{0, 0} Lat →
            ∀ (v : V),
              Membership.mem.{0, 0}
                  (Submodule.span.{0, 0} O (Set.image.{0, 0} (DFunLike.coe.{1, 1, 1} cmp) (SetLike.coe.{0, 0} Lat)))
                  (DFunLike.coe.{1, 1, 1} cmp v) →
                Exists.{1} fun (s : A) ↦
                  And (Not (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} w) s))
                    (Membership.mem.{0, 0} Lat (HSMul.hSMul.{0, 0, 0} s v)) := by sorry
