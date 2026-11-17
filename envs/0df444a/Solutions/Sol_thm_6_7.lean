-- Prove2me | solution 1 for thm_6_7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:31:22.421198+00:00
-- url     : https://prove2.me/submissions/fd8f2314-e2c9-4197-b53a-04297693df2b

import Theorems.Thm_Thm67Support_ae_eq_realCoe_toReal
import Theorems.Thm_Thm67Support_integrable_toReal
import Theorems.Thm_Thm67Support_realCoe_textbookIntegrable_iff
import Theorems.Thm_Thm67Support_textbookIntegrable_congr_ae
import Theorems.Thm_Thm67Support_textbookIntegral_congr_ae
import Theorems.Thm_Thm67Support_textbookIntegral_realCoe_eq_some_integral
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic


/-! # Theorem 6.7: linearity of the Lebesgue integral -/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace Thm67Support

end Thm67Support


private theorem source_thm67_integrable_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) (α : ℝ) :
    textbookIntegrable μ (fun ω => X ω + Y ω) := by
  have h_add : textbookIntegrable μ (fun ω => (X ω).toReal + (Y ω).toReal) := by
    convert Thm67Support.realCoe_textbookIntegrable_iff _ |>.2 ( Thm67Support.integrable_toReal hXm hX |> fun h => h.add ( Thm67Support.integrable_toReal hYm hY ) ) using 1;
    · rfl
    · exact hXm.ereal_toReal.add hYm.ereal_toReal
  have h_eq : ∀ᵐ ω ∂μ, X ω + Y ω = (X ω).toReal + (Y ω).toReal := by
    have h_eq : ∀ᵐ ω ∂μ, X ω = (X ω).toReal ∧ Y ω = (Y ω).toReal := by
      have := Thm67Support.ae_eq_realCoe_toReal hXm hX; have := Thm67Support.ae_eq_realCoe_toReal hYm hY; aesop;
    filter_upwards [ h_eq ] with ω hω using congr_arg₂ ( · + · ) hω.1 hω.2;
  exact (Thm67Support.textbookIntegrable_congr_ae h_eq).mpr h_add;

private theorem source_thm67_integral_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) (α : ℝ) :
    textbookIntegral μ (fun ω => X ω + Y ω) =
        Option.map₂ (fun x y => x + y) (textbookIntegral μ X) (textbookIntegral μ Y) := by
  convert Thm67Support.textbookIntegral_congr_ae _ |> Eq.trans <| Thm67Support.textbookIntegral_realCoe_eq_some_integral _ using 1;
  case convert_6 => exact fun ω => ( X ω |> EReal.toReal ) + ( Y ω |> EReal.toReal );
  · have := Thm67Support.textbookIntegral_realCoe_eq_some_integral ( Thm67Support.integrable_toReal hXm hX ) ; have := Thm67Support.textbookIntegral_realCoe_eq_some_integral ( Thm67Support.integrable_toReal hYm hY ) ; simp_all +decide [ Option.map₂ ] ;
    rw [ MeasureTheory.integral_add ];
    · rw [ Thm67Support.textbookIntegral_congr_ae ( Thm67Support.ae_eq_realCoe_toReal hXm hX ), Thm67Support.textbookIntegral_congr_ae ( Thm67Support.ae_eq_realCoe_toReal hYm hY ) ] ; aesop;
    · exact Thm67Support.integrable_toReal hXm hX;
    · exact Thm67Support.integrable_toReal hYm hY;
  · filter_upwards [ Thm67Support.ae_eq_realCoe_toReal hXm hX, Thm67Support.ae_eq_realCoe_toReal hYm hY ] with ω hωX hωY;
    rw [ hωX, hωY, EReal.coe_add ];
    norm_num;
  · exact MeasureTheory.Integrable.add ( Thm67Support.integrable_toReal hXm hX ) ( Thm67Support.integrable_toReal hYm hY );

private theorem source_thm67_integrable_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) (α : ℝ) :
    textbookIntegrable μ (fun ω => ((α : EReal) * X ω)) := by
  convert Thm67Support.textbookIntegrable_congr_ae _ |>.2 ( Thm67Support.realCoe_textbookIntegrable_iff ( show Measurable fun ω => ( α * ( X ω |> EReal.toReal ) ) from ?_ ) |>.2 ( ?_ ) ) using 1;
  · filter_upwards [ Thm67Support.ae_eq_realCoe_toReal hXm hX ] with ω hω;
    rw [ hω ] ; norm_cast;
  · fun_prop;
  · exact MeasureTheory.Integrable.const_mul ( Thm67Support.integrable_toReal hXm hX ) α;

private theorem source_thm67_integral_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) (α : ℝ) :
    textbookIntegral μ (fun ω => ((α : EReal) * X ω)) =
        Option.map (fun x => (α : EReal) * x) (textbookIntegral μ X) := by
  convert Thm67Support.textbookIntegral_congr_ae _ |> Eq.trans <| Thm67Support.textbookIntegral_realCoe_eq_some_integral _ using 1;
  convert congr_arg ( fun x : Option EReal => Option.map ( fun y : EReal => ( α : EReal ) * y ) x ) ( Thm67Support.textbookIntegral_realCoe_eq_some_integral <| Thm67Support.integrable_toReal hXm hX ) using 1;
  convert congr_arg ( fun x : Option EReal => Option.map ( fun y : EReal => ( α : EReal ) * y ) x ) ( Thm67Support.textbookIntegral_congr_ae _ ) using 1;
  exact Thm67Support.ae_eq_realCoe_toReal hXm hX;
  rotate_left;
  rotate_left;
  exact fun ω => α * ( X ω |> EReal.toReal );
  · exact MeasureTheory.Integrable.const_mul ( Thm67Support.integrable_toReal hXm hX ) α;
  · simp [ MeasureTheory.integral_const_mul ];
  · filter_upwards [ Thm67Support.ae_eq_realCoe_toReal hXm hX ] with ω hω;
    rw [ hω ] ; norm_cast

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) (α : ℝ) :
    textbookIntegrable μ (fun ω => X ω + Y ω) ∧
      textbookIntegral μ (fun ω => X ω + Y ω) =
        Option.map₂ (fun x y => x + y) (textbookIntegral μ X) (textbookIntegral μ Y) ∧
      textbookIntegrable μ (fun ω => ((α : EReal) * X ω)) ∧
      textbookIntegral μ (fun ω => ((α : EReal) * X ω)) =
        Option.map (fun x => (α : EReal) * x) (textbookIntegral μ X) := by
  exact ⟨source_thm67_integrable_add μ hXm hYm hX hY α, source_thm67_integral_add μ hXm hYm hX hY α, source_thm67_integrable_mul μ hXm hYm hX hY α, source_thm67_integral_mul μ hXm hYm hX hY α⟩
