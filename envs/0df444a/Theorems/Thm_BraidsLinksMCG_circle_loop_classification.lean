-- Prove2me | Theorems.Thm_BraidsLinksMCG_circle_loop_classification
-- name    : BraidsLinksMCG.circle_loop_classification
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-28T21:07:52.349589+00:00
-- url     : https://prove2.me/theorems/26be8809-8d60-4f45-9b4f-c3e551d6b781
-- title:
--   Every loop in a circle is homotopic to an explicit winding loop
-- statement:
--   For a circle {z : ℂ | ‖z - c‖ = r} with r > 0, every loop based at c + r is homotopic relative to the basepoint to the explicit winding-k loop t ↦ c + r·exp(2πikt) for some integer k. The proof goes through the covering map s ↦ c + r·exp(2πis) from ℝ, obtained by restricting the exponential covering of ℂˣ to the norm-r fiber; a lifted path ends at an integer, and the straight-line homotopy in ℝ projects to the desired based homotopy in the circle.
-- source:
--   proofs_vankampen/right_piece_DECOMPOSITION.md (Theorem A: every loop in the circle is path-homotopic to a winding power; deep input for BraidsLinksMCG.puncturedPlane_succ_right_piece_range_v1, standalone module per the decomposition recommendation)

import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

variable (c : ℂ) (r : ℝ)

namespace BraidsLinksMCG

/-- The circle of radius `r` about `c`. -/
def circleSet : Set ℂ := {z : ℂ | ‖z - c‖ = r}

/-- The basepoint `c + r` on the circle. -/
noncomputable def circleBase (hr : 0 < r) : ↥(circleSet c r) :=
  ⟨c + r, by
    show ‖c + (r : ℂ) - c‖ = r
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]⟩

/-- The explicit winding-`k` loop around the circle, based at `circleBase`. -/
noncomputable def circleWind (k : ℤ) (hr : 0 < r) :
    Path (circleBase c r hr) (circleBase c r hr) where
  toFun t := ⟨c + r * Complex.exp (2 * Real.pi * (k : ℝ) * t.1 * Complex.I), by
    show ‖c + ↑r * Complex.exp (2*↑Real.pi*↑(k:ℝ)*↑t.1*Complex.I) - c‖ = r
    rw [add_sub_cancel_left, norm_mul]
    have hexp : ‖Complex.exp (2*↑Real.pi*↑(k:ℝ)*↑t.1*Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      have h0 : (2*↑Real.pi*↑(k:ℝ)*↑t.1*Complex.I).re = 0 := by simp
      rw [h0, Real.exp_zero]
    rw [hexp, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := by
    apply Subtype.ext
    show c + ↑r * Complex.exp (2*↑Real.pi*↑(k:ℝ)*0*Complex.I) = c + ↑r
    simp
  target' := by
    apply Subtype.ext
    show c + ↑r * Complex.exp (2*↑Real.pi*↑(k:ℝ)*1*Complex.I) = c + ↑r
    have hexp : Complex.exp (2*↑Real.pi*↑(k:ℝ)*1*Complex.I) = 1 := by
      have hkk : (2*↑Real.pi*↑(k:ℝ)*1*Complex.I : ℂ)
          = ((k:ℤ):ℂ) * (2 * ↑Real.pi * Complex.I) := by push_cast; ring
      rw [hkk, Complex.exp_int_mul_two_pi_mul_I]
    rw [hexp, mul_one]

section Covering

variable {c : ℂ} {r : ℝ} (hr : 0 < r)

/-- `Complex.exp` viewed as landing in `ℂˣ`-as-subtype, matching
`Complex.isCoveringMap_exp`. -/
noncomputable def expSub : ℂ → {z : ℂ // z ≠ 0} :=
  fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})

/-- The norm-`r` fiber inside `ℂˣ`-as-subtype. -/
def tSet : Set {z : ℂ // z ≠ 0} := {w | ‖(w.val : ℂ)‖ = r}

/-- `ℝ` is homeomorphic to the preimage of the norm-`r` fiber under `expSub`,
via `s ↦ log r + 2πis`. -/
noncomputable def fiberHomeo : ℝ ≃ₜ ↥(expSub ⁻¹' (tSet (r := r))) where
  toFun s := ⟨(Real.log r : ℂ) + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I, by
    show ‖Complex.exp ((Real.log r : ℂ) + ((2*Real.pi*s : ℝ):ℂ) * Complex.I)‖ = r
    rw [Complex.exp_add]
    have e1 : Complex.exp ((Real.log r : ℂ)) = (r : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hr]
    have e2 : ‖Complex.exp (((2*Real.pi*s : ℝ):ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      have h0 : ((((2*Real.pi*s : ℝ):ℂ)) * Complex.I).re = 0 := by simp
      rw [h0, Real.exp_zero]
    rw [norm_mul, e1, e2, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]⟩
  invFun z := z.val.im / (2 * Real.pi)
  left_inv := by
    intro s
    show ((((Real.log r : ℂ) + ((2*Real.pi*s : ℝ):ℂ) * Complex.I)).im / (2 * Real.pi)) = s
    have him : ((((Real.log r : ℂ) + ((2*Real.pi*s : ℝ):ℂ) * Complex.I)).im)
        = 2*Real.pi*s := by simp
    have h2pi : (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
    rw [him, div_eq_iff h2pi]
    ring
  right_inv := by
    intro w
    have hmem : ‖Complex.exp w.val‖ = r := w.2
    have hre : w.val.re = Real.log r := by
      have h1 : Real.exp w.val.re = r := by
        have h2 := hmem
        rwa [Complex.norm_exp] at h2
      have h2 := congrArg Real.log h1
      rwa [Real.log_exp] at h2
    have h2pi : (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
    apply Subtype.ext
    show (Real.log r : ℂ) + ((2*Real.pi*(w.val.im/(2*Real.pi)) : ℝ):ℂ) * Complex.I
      = w.val
    have h3 : (2*Real.pi*(w.val.im/(2*Real.pi)) : ℝ) = w.val.im := by
      field_simp
    rw [h3, ← hre]
    exact Complex.re_add_im w.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by fun_prop

/-- The norm-`r` fiber is homeomorphic to the geometric circle, via `w ↦ c + w`. -/
noncomputable def circleHomeo : ↥(tSet (r := r)) ≃ₜ ↥(circleSet c r) where
  toFun w := ⟨c + (w.val.val : ℂ), by
    have h2 := w.2
    show ‖c + (w.val.val : ℂ) - c‖ = r
    rw [add_sub_cancel_left]
    exact h2⟩
  invFun z := ⟨⟨z.val - c, by
      have h2 : ‖z.val - c‖ = r := z.2
      intro hcon
      rw [hcon, norm_zero] at h2
      linarith⟩,
    by
      show (⟨z.val - c, by
        have h2 : ‖z.val - c‖ = r := z.2
        intro hcon
        rw [hcon, norm_zero] at h2
        linarith⟩ : {z : ℂ // z ≠ 0}) ∈ tSet
      show ‖z.val - c‖ = r
      exact z.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    apply Subtype.ext
    show c + w.val.val - c = w.val.val
    abel
  right_inv := by
    intro z
    apply Subtype.ext
    show c + (z.val - c) = z.val
    abel
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The covering map `ℝ → circleSet c r`, `s ↦ c + r·exp(2πis)`. -/
noncomputable def circleCover : ℝ → ↥(circleSet c r) :=
  fun s => ⟨c + r * Complex.exp (2 * Real.pi * s * Complex.I), by
    show ‖c + ↑r * Complex.exp (2*↑Real.pi*↑s*Complex.I) - c‖ = r
    rw [add_sub_cancel_left, norm_mul]
    have hexp : ‖Complex.exp (2*↑Real.pi*↑s*Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      have h0 : (2*↑Real.pi*↑s*Complex.I).re = 0 := by simp
      rw [h0, Real.exp_zero]
    rw [hexp, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]⟩

/-- **Theorem A (classification of loops in a circle).** Every loop in the
circle `{z : ℂ | ‖z - c‖ = r}` based at `c + r` is homotopic (relative to the
basepoint) to the explicit winding-`k` loop `circleWind c r k hr` for some
`k : ℤ`. -/
theorem circle_loop_classification (δ : Path (circleBase c r hr) (circleBase c r hr)) :
    ∃ k : ℤ, δ.Homotopic (circleWind c r k hr) := by
  sorry

end Covering

end BraidsLinksMCG
