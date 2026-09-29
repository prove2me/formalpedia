-- Prove2me | solution 1 for deriv_deriv_comm_of_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/65345bd9-a1ed-5e83-a9da-5f0dca923351

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_deriv_deriv_comm_of_contDiffOn

set_option autoImplicit false

namespace S1aAsm

theorem nested_eq (f : ℝ × ℝ → ℂ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ U)
    (hf : ContDiffOn ℝ 2 f U)
    (a b : ℝ × ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => f (s • a + t • b)) 0) 0 = fderiv ℝ (fderiv ℝ f) (0, 0) a b := by

  have hdiff : ∀ p ∈ U, DifferentiableAt ℝ f p := fun p hp =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hf0 : ContDiffAt ℝ 2 f (0, 0) := hf.contDiffAt (hU.mem_nhds h0)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (0, 0) :=
    (hf0.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

  have hnear : ∀ᶠ s in nhds (0 : ℝ), deriv (fun t : ℝ => f (s • a + t • b)) 0 = fderiv ℝ f (s • a) b := by
    have hc : Continuous fun s : ℝ => s • a := continuous_id.smul continuous_const
    have hop : IsOpen ((fun s : ℝ => s • a) ⁻¹' U) := hc.isOpen_preimage U hU
    have hmem : (0 : ℝ) ∈ (fun s : ℝ => s • a) ⁻¹' U := by simp at h0 ⊢; exact h0
    filter_upwards [hop.mem_nhds hmem] with s hs
    have hcurve : HasDerivAt (fun t : ℝ => s • a + t • b) b 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add (s • a)
      simpa using this
    have hcomp := (hdiff _ hs).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
    exact hcomp.deriv
  rw [Filter.EventuallyEq.deriv_eq hnear]

  have hcurve : HasDerivAt (fun s : ℝ => s • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • a)) (fderiv ℝ (fderiv ℝ f) (0, 0) a) 0 :=
    hfd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • a) b) (fderiv ℝ (fderiv ℝ f) (0, 0) a b) 0 := by
    have := h1.clm_apply (hasDerivAt_const (0 : ℝ) b)
    simpa using this
  exact h2.deriv

end S1aAsm

theorem solution
    (F : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ U)
    (hF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) U) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F s t) 0) 0
      = deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0 := by
  set f : ℝ × ℝ → ℂ := fun p => F p.1 p.2 with hf
  have hsymm : IsSymmSndFDerivAt ℝ f (0, 0) :=
    (hF.contDiffAt (hU.mem_nhds h0)).isSymmSndFDerivAt (by simp)
  have e1 : deriv (fun s : ℝ => deriv (fun t : ℝ => F s t) 0) 0
      = deriv (fun s : ℝ => deriv (fun t : ℝ => f (s • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)))) 0) 0 := by
    congr 1; funext s; congr 1; funext t; simp [hf]
  have e2 : deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0
      = deriv (fun t : ℝ => deriv (fun s : ℝ => f (t • ((0 : ℝ), (1 : ℝ)) + s • ((1 : ℝ), (0 : ℝ)))) 0) 0 := by
    congr 1; funext t; congr 1; funext s; simp [hf]
  rw [e1, e2, S1aAsm.nested_eq f U hU h0 hF, S1aAsm.nested_eq f U hU h0 hF]
  exact hsymm _ _

end S_deriv_deriv_comm_of_contDiffOn
end P2MW
export P2MW.S_deriv_deriv_comm_of_contDiffOn (solution)
