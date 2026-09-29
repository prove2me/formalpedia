-- Prove2me | solution 1 for fta_winding_homotopy_preserves_lift
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-05-22T15:04:08.191495+00:00
-- url     : https://prove2.me/submissions/9d59a3ac-3ce2-4122-9a17-db418e7434f7

import Definitions.Def_fta_winding_infra

open scoped unitInterval

theorem solution (γ δ : FtaCircle → Circle)
    (hhom : FtaCircleHomotopic γ δ) (hlift : FtaHasLift γ) :
    FtaHasLift δ := by
  rcases hhom with ⟨H, hH0, hH1⟩
  rcases hlift with ⟨Γ, hΓ_cont, hΓ⟩
  let Γc : C(FtaCircle, ℝ) := ⟨Γ, hΓ_cont⟩
  have H0 : ∀ θ : FtaCircle, H (0, θ) = Circle.exp (Γc θ) := by
    intro θ
    exact (hH0 θ).trans (hΓ θ).symm
  let L : C(I × FtaCircle, ℝ) := Circle.isCoveringMap_exp.liftHomotopy H Γc H0
  refine ⟨fun θ : FtaCircle => L (1, θ), ?_, ?_⟩
  · fun_prop
  · intro θ
    have hL := congr_fun (Circle.isCoveringMap_exp.liftHomotopy_lifts H Γc H0) (1, θ)
    exact hL.trans (hH1 θ)
