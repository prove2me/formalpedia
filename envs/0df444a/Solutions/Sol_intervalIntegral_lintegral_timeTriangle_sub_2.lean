-- Prove2me | solution 2 for intervalIntegral.lintegral_timeTriangle_sub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:07:02.127681+00:00
-- url     : https://prove2.me/submissions/75417b71-6610-4021-b601-2961f7d07c26

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Theorems.Thm_triangle_lintegral_identity_06d84b44
import Theorems.Thm_triangle_lintegral_identity_b176d7f6

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open intervalIntegral
noncomputable section

theorem solution {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u) := by
  let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}
  let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hF : Measurable F := by
    exact (hh.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))).indicator hS
  have hleft : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ t, ∫⁻ s, F (s, t) := triangle_lintegral_identity_06d84b44 (h := h) (hh := hh) (hS := hS) (hF := hF)
  have hright : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u)) =
      ∫⁻ s, ∫⁻ u, F (s, s + u) := triangle_lintegral_identity_b176d7f6 (h := h) (hh := hh) (hS := hS) (hF := hF) (hleft := hleft)
  rw [hleft, hright]
  have hFswap : Measurable fun p : ℝ × ℝ ↦ F (p.2, p.1) :=
    hF.comp measurable_swap
  calc
    (∫⁻ t, ∫⁻ s, F (s, t)) = ∫⁻ s, ∫⁻ t, F (s, t) :=
      lintegral_lintegral_swap hFswap.aemeasurable
    _ = ∫⁻ p, F p ∂volume.prod volume :=
      (lintegral_prod F hF.aemeasurable).symm
    _ = ∫⁻ p, F (p.1, p.1 + p.2) ∂volume.prod volume := by
      exact ((measurePreserving_prod_add volume volume).lintegral_comp_emb
        (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding F).symm
    _ = ∫⁻ s, ∫⁻ u, F (s, s + u) := lintegral_prod _ (hF.comp
      (measurable_fst.prodMk measurable_add)).aemeasurable
