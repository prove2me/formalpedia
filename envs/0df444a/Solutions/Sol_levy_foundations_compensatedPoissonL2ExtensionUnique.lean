-- Prove2me | solution 1 for levy_foundations_compensatedPoissonL2ExtensionUnique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:57:02.319653+00:00
-- url     : https://prove2.me/submissions/ba80cbb3-4d8f-4dbc-a459-273eaf3f86e5

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (I J : Lp ℝ 2 m → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension m μ K X I)
    (hJ : LevyFoundations.IsCompensatedPoissonL2Extension m μ K X J) :
    I = J := by
  have hIsub (f g : Lp ℝ 2 m) : I (f - g) = I f - I g := by
    have hneg : I (-g) = -I g := by
      simpa only [neg_one_smul] using hI.map_smul (-1 : ℝ) g
    simpa only [sub_eq_add_neg, hI.map_add, hneg]
  have hJsub (f g : Lp ℝ 2 m) : J (f - g) = J f - J g := by
    have hneg : J (-g) = -J g := by
      simpa only [neg_one_smul] using hJ.map_smul (-1 : ℝ) g
    simpa only [sub_eq_add_neg, hJ.map_add, hneg]
  have hIc : Continuous I := by
    apply Isometry.continuous
    intro f g
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm,
      ← hIsub f g, hI.norm_eq]
  have hJc : Continuous J := by
    apply Isometry.continuous
    intro f g
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm,
      ← hJsub f g, hJ.norm_eq]
  have hclosed : IsClosed {f : Lp ℝ 2 m | I f = J f} :=
    isClosed_eq hIc hJc
  have hindicator (c : ℝ) {s : Set E}
      (hs : MeasurableSet s) (hms : m s < ⊤) :
      I (↑(Lp.simpleFunc.indicatorConst 2 hs hms.ne c) : Lp ℝ 2 m) =
      J (↑(Lp.simpleFunc.indicatorConst 2 hs hms.ne c) : Lp ℝ 2 m) := by
    let f : E → ℝ := s.indicator (fun _ => c)
    have hf2 : MemLp f 2 m :=
      memLp_indicator_const 2 hs c (Or.inr hms.ne)
    have hf1 : Integrable f m :=
      memLp_one_iff_integrable.mp
        (memLp_indicator_const 1 hs c (Or.inr hms.ne))
    have hfm : Measurable f := measurable_const.indicator hs
    have heq : (fun ω => I (hf2.toLp f) ω) =ᵐ[μ]
        (fun ω => J (hf2.toLp f) ω) :=
      (hI.agree_sum f hfm hf1 hf2).trans
        (hJ.agree_sum f hfm hf1 hf2).symm
    have heqLp : I (hf2.toLp f) = J (hf2.toLp f) := Lp.ext heq
    have hid : hf2.toLp f =
        (↑(Lp.simpleFunc.indicatorConst 2 hs hms.ne c) : Lp ℝ 2 m) := by
      rw [Lp.simpleFunc.coe_indicatorConst]
      rfl
    rw [← hid]
    exact heqLp
  apply funext
  intro f
  exact Lp.induction (by norm_num)
    (fun z : Lp ℝ 2 m => I z = J z)
    (fun c s hs hms => hindicator c hs hms)
    (by
      intro a b ha hb hab hia hib
      calc
        I (ha.toLp a + hb.toLp b) =
            I (ha.toLp a) + I (hb.toLp b) := hI.map_add _ _
        _ = J (ha.toLp a) + J (hb.toLp b) := by rw [hia, hib]
        _ = J (ha.toLp a + hb.toLp b) := (hJ.map_add _ _).symm)
    hclosed f