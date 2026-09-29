-- Prove2me | solution 1 for deriv_deriv_deriv_reverse_of_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4664be8b-fd2c-54cb-aab1-c5f7046198c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_deriv_deriv_deriv_reverse_of_contDiffOn

set_option autoImplicit false

namespace S1bAsm

theorem hasDerivAt_comp_line {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : ℝ × ℝ × ℝ → F') (L' : (ℝ × ℝ × ℝ) →L[ℝ] F') (a p : ℝ × ℝ × ℝ) (hp : p = (0 : ℝ) • a)
    (hL : HasFDerivAt L L' p) : HasDerivAt (fun s : ℝ => L (s • a)) (L' a) 0 := by
  have hcurve : HasDerivAt (fun s : ℝ => s • a) a 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  exact hL.comp_hasDerivAt_of_eq (0 : ℝ) hcurve hp

variable (f : ℝ × ℝ × ℝ → ℂ) (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ U)
  (hf : ContDiffOn ℝ 3 f U)

include hU hf in
theorem contDiffAt_of_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ U) : ContDiffAt ℝ 3 f p := hf.contDiffAt (hU.mem_nhds hp)

include hU hf in

theorem level1 {q : ℝ × ℝ × ℝ} (hq : q ∈ U) (c : ℝ × ℝ × ℝ) :
    deriv (fun u : ℝ => f (q + u • c)) 0 = fderiv ℝ f q c := by
  have hd : DifferentiableAt ℝ f q := (contDiffAt_of_mem f U hU hf hq).differentiableAt (by norm_num)
  have hcurve : HasDerivAt (fun u : ℝ => q + u • c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add q
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)).deriv

include hU hf in

theorem level2 {q : ℝ × ℝ × ℝ} (hq : q ∈ U) (b c : ℝ × ℝ × ℝ) :
    deriv (fun t : ℝ => deriv (fun u : ℝ => f (q + t • b + u • c)) 0) 0 = fderiv ℝ (fderiv ℝ f) q b c := by
  have hnear : ∀ᶠ t in nhds (0 : ℝ), deriv (fun u : ℝ => f (q + t • b + u • c)) 0 = fderiv ℝ f (q + t • b) c := by
    have hc : Continuous fun t : ℝ => q + t • b := continuous_const.add (continuous_id.smul continuous_const)
    filter_upwards [(hc.isOpen_preimage U hU).mem_nhds (by simpa using hq)] with t ht
    exact level1 f U hU hf ht c
  rw [Filter.EventuallyEq.deriv_eq hnear]
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    ((contDiffAt_of_mem f U hU hf hq).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hcurve : HasDerivAt (fun t : ℝ => q + t • b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add q
  have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ f (q + t • b)) (fderiv ℝ (fderiv ℝ f) q b) 0 :=
    hfd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
  have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) c)
  simp only [zero_smul, add_zero, map_zero, ContinuousLinearMap.zero_apply] at h2
  exact h2.deriv

include hU h0 hf in

theorem level3 (a b c : ℝ × ℝ × ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => deriv (fun u : ℝ => f (s • a + t • b + u • c)) 0) 0) 0
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) a b c := by
  have hnear : ∀ᶠ s in nhds (0 : ℝ), deriv (fun t : ℝ => deriv (fun u : ℝ => f (s • a + t • b + u • c)) 0) 0
      = fderiv ℝ (fderiv ℝ f) (s • a) b c := by
    have hc : Continuous fun s : ℝ => s • a := continuous_id.smul continuous_const
    filter_upwards [(hc.isOpen_preimage U hU).mem_nhds (by simp at h0 ⊢; exact h0)] with s hs
    exact level2 f U hU hf hs b c
  rw [Filter.EventuallyEq.deriv_eq hnear]
  have hffd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    have h3 : ContDiffAt ℝ 3 f (0, 0, 0) := contDiffAt_of_mem f U hU hf h0
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) (0, 0, 0) := h3.fderiv_right (m := 2) (by norm_num)
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) := h2.fderiv_right (m := 1) (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ f) (s • a)) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) a) 0 :=
    hasDerivAt_comp_line (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) ((0 : ℝ), (0 : ℝ), (0 : ℝ))) a ((0 : ℝ), (0 : ℝ), (0 : ℝ)) (by simp) hffd.hasFDerivAt
  have h2 := (h1.clm_apply (hasDerivAt_const (0 : ℝ) b)).clm_apply (hasDerivAt_const (0 : ℝ) c)
  simp only [map_zero, ContinuousLinearMap.zero_apply, add_zero] at h2
  exact h2.deriv

include hU h0 hf in

theorem swap23 (a b c : ℝ × ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) a b c = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) a c b := by

  have hsym : ∀ᶠ s in nhds (0 : ℝ), fderiv ℝ (fderiv ℝ f) (s • a) b c = fderiv ℝ (fderiv ℝ f) (s • a) c b := by
    have hc : Continuous fun s : ℝ => s • a := continuous_id.smul continuous_const
    filter_upwards [(hc.isOpen_preimage U hU).mem_nhds (by simp at h0 ⊢; exact h0)] with s hs
    exact (contDiffAt_of_mem f U hU hf hs).isSymmSndFDerivAt (le_trans (by simp : minSmoothness ℝ 2 ≤ 2) (by norm_num)) b c
  have key : ∀ b c : ℝ × ℝ × ℝ, deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ f) (s • a) b c) 0
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) a b c := by
    intro b c
    have hffd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := by
      have h3 : ContDiffAt ℝ 3 f (0, 0, 0) := contDiffAt_of_mem f U hU hf h0
      have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) (0, 0, 0) := h3.fderiv_right (m := 2) (by norm_num)
      have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) := h2.fderiv_right (m := 1) (by norm_num)
      exact h1.differentiableAt (by norm_num)
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ f) (s • a)) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) a) 0 :=
      hasDerivAt_comp_line (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) ((0 : ℝ), (0 : ℝ), (0 : ℝ))) a ((0 : ℝ), (0 : ℝ), (0 : ℝ)) (by simp) hffd.hasFDerivAt
    have h2 := (h1.clm_apply (hasDerivAt_const (0 : ℝ) b)).clm_apply (hasDerivAt_const (0 : ℝ) c)
    simp only [map_zero, ContinuousLinearMap.zero_apply, add_zero] at h2
    exact h2.deriv
  rw [← key b c, ← key c b]
  exact Filter.EventuallyEq.deriv_eq hsym

include hU h0 hf in

theorem swap12 (a b c : ℝ × ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) a b c = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (0, 0, 0) b a c := by
  have h3 : ContDiffAt ℝ 3 f (0, 0, 0) := contDiffAt_of_mem f U hU hf h0
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) (0, 0, 0) := h3.fderiv_right (m := 2) (by norm_num)
  have := h2.isSymmSndFDerivAt (by simp) a b
  rw [this]

end S1bAsm

theorem solution
    (G : ℝ → ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ U)
    (hG : ContDiffOn ℝ 3 (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) U) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => deriv (fun u : ℝ => G s t u) 0) 0) 0
      = deriv (fun u : ℝ => deriv (fun t : ℝ => deriv (fun s : ℝ => G s t u) 0) 0) 0 := by
  set f : ℝ × ℝ × ℝ → ℂ := fun p => G p.1 p.2.1 p.2.2 with hf
  set e₁ : ℝ × ℝ × ℝ := ((1 : ℝ), (0 : ℝ), (0 : ℝ))
  set e₂ : ℝ × ℝ × ℝ := ((0 : ℝ), (1 : ℝ), (0 : ℝ))
  set e₃ : ℝ × ℝ × ℝ := ((0 : ℝ), (0 : ℝ), (1 : ℝ))
  have l1 : deriv (fun s : ℝ => deriv (fun t : ℝ => deriv (fun u : ℝ => G s t u) 0) 0) 0
      = deriv (fun s : ℝ => deriv (fun t : ℝ => deriv (fun u : ℝ => f (s • e₁ + t • e₂ + u • e₃)) 0) 0) 0 := by
    congr 1; funext s; congr 1; funext t; congr 1; funext u; simp [hf, e₁, e₂, e₃]
  have l2 : deriv (fun u : ℝ => deriv (fun t : ℝ => deriv (fun s : ℝ => G s t u) 0) 0) 0
      = deriv (fun u : ℝ => deriv (fun t : ℝ => deriv (fun s : ℝ => f (u • e₃ + t • e₂ + s • e₁)) 0) 0) 0 := by
    congr 1; funext u; congr 1; funext t; congr 1; funext s; simp [hf, e₁, e₂, e₃]
  rw [l1, l2, S1bAsm.level3 f U hU h0 hG, S1bAsm.level3 f U hU h0 hG]

  rw [S1bAsm.swap12 f U hU h0 hG e₁ e₂ e₃, S1bAsm.swap23 f U hU h0 hG e₂ e₁ e₃, S1bAsm.swap12 f U hU h0 hG e₂ e₃ e₁]

end S_deriv_deriv_deriv_reverse_of_contDiffOn
end P2MW
export P2MW.S_deriv_deriv_deriv_reverse_of_contDiffOn (solution)
