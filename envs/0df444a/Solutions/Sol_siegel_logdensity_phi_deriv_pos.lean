-- Prove2me | solution 1 for siegel_logdensity_phi_deriv_pos
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T18:51:19.106902+00:00
-- url     : https://prove2.me/submissions/6d9f53d4-56e7-42ff-ba54-774449e3ff26

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
open Set

/-- **Siegel 2001 "Median Bounds and their Application" (J. Algorithms 38:184-236),
Theorem 2.2 / §2.1.1 — the φ'-sign step.**

For the waiting-time log-density `G(t) = m·log(1 - e^{-λt}) - (N-m)·λ·t`
(= `log f(t)` up to the additive constant `log K` for the Siegel density
`f(t) = K (1-e^{-λt})^m (e^{-λt})^{N-m}`), set the symmetrized log-ratio
`φ(t) = G(t) - G(2µ - t)`.

Under the "small-mean" condition `(N-m)·e^{λµ} < N`  (equivalently `e^{λµ} < N/(N-m)`,
which `µ = E[T] = (1/λ)∑_{N-m+1}^{N} 1/j < (1/λ)log(N/(N-m))` satisfies), the
derivative `φ'(t) = G'(t) + G'(2µ-t)` is **strictly positive** for every `t ∈ (0,µ)`,
where `G'(s) = m·λ·e^{-λs}/(1-e^{-λs}) - (N-m)·λ`.

Proof: chain rule gives `HasDerivAt`; for the sign, with `α = e^{λt}-1 > 0`,
`β = e^{λ(2µ-t)}-1 > 0`, one has `φ'(t) = λ·(m/α + m/β - 2(N-m))`, and
`m/α + m/β > 2(N-m)` reduces (clearing the positive denominator `αβ`, using
`α+β = e^{λt}+e^{λ(2µ-t)}-2 ≥ 2e^{λµ}-2` by AM-GM since `e^{λt}·e^{λ(2µ-t)} = e^{2λµ}`,
and `αβ = e^{2λµ} - (e^{λt}+e^{λ(2µ-t)}) + 1`) to the factorisation
`(e^{λµ}-1)·((N-m)e^{λµ} - N) < 0`, which holds since `e^{λµ}>1` and `(N-m)e^{λµ}<N`.
This is the (single-)turning-point analysis underlying Siegel's moustache argument;
here the discriminant is negative so `φ` is in fact monotone increasing on `(0,µ)`. -/
theorem solution
    (lam m Nn mu : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hmN : m < Nn) (hmu : 0 < mu)
    (hcond : (Nn - m) * Real.exp (lam * mu) < Nn) :
    ∀ t ∈ Ioo (0:ℝ) mu,
      HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y))
                    - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y))))
        ( (m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)
          + (m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam) ) t
      ∧ 0 < ( (m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)
          + (m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam) ) := by
  -- local abbreviations matching the inlined formulas
  set Glog : ℝ → ℝ := fun t => m * Real.log (1 - Real.exp (-lam * t)) - (Nn - m) * (lam * t) with hGlog
  set GlogD : ℝ → ℝ := fun t => m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam with hGlogD
  -- derivative of Glog at any s>0
  have hasD : ∀ s : ℝ, 0 < s → HasDerivAt Glog (GlogD s) s := by
    intro s hs
    rw [hGlog, hGlogD]
    have hexp : HasDerivAt (fun y => Real.exp (-lam * y)) (-lam * Real.exp (-lam * s)) s := by
      have := (((hasDerivAt_id s).const_mul (-lam)).exp); simpa [mul_comm] using this
    have hone : HasDerivAt (fun y => 1 - Real.exp (-lam * y)) (lam * Real.exp (-lam * s)) s := by
      have := hexp.const_sub 1; simpa using this
    have hposne : (1 : ℝ) - Real.exp (-lam * s) ≠ 0 := by
      have : Real.exp (-lam * s) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
      linarith
    have hlog : HasDerivAt (fun y => Real.log (1 - Real.exp (-lam * y)))
        ((lam * Real.exp (-lam * s)) / (1 - Real.exp (-lam * s))) s := hone.log hposne
    have hlin : HasDerivAt (fun y => (Nn - m) * (lam * y)) ((Nn - m) * lam) s := by
      have h2 := ((hasDerivAt_id s).const_mul lam).const_mul (Nn - m); simpa [mul_assoc] using h2
    have hd := (hlog.const_mul m).fun_sub hlin
    exact hd
  -- main
  intro t ht
  obtain ⟨ht0, htmu⟩ := ht
  have hpt : (0:ℝ) < 2*mu - t := by linarith
  -- derivative of φ
  have hderiv : HasDerivAt (fun y => Glog y - Glog (2*mu - y)) (GlogD t + GlogD (2*mu - t)) t := by
    have h1 := hasD t ht0
    have hinner : HasDerivAt (fun y => 2*mu - y) (-1 : ℝ) t := by
      have := (hasDerivAt_id t).const_sub (2*mu); simpa using this
    have h2 := hasD (2*mu - t) hpt
    have hcomp : HasDerivAt (fun y => Glog (2*mu - y)) (GlogD (2*mu - t) * (-1)) t := h2.comp t hinner
    have hd := h1.fun_sub hcomp
    exact hd.congr_deriv (by ring)
  -- positivity of φ'
  have hpos : 0 < GlogD t + GlogD (2*mu - t) := by
    have hNm : 0 < Nn - m := by linarith
    have hlt : Real.exp (-lam * t) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
    have hlt2 : Real.exp (-lam * (2*mu - t)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
    set a : ℝ := 1 - Real.exp (-lam * t) with ha
    set b : ℝ := 1 - Real.exp (-lam * (2*mu - t)) with hb
    have hapos : 0 < a := by rw [ha]; linarith
    have hbpos : 0 < b := by rw [hb]; linarith
    have key : GlogD t + GlogD (2*mu - t)
        = lam * ( m * (Real.exp (-lam*t) / a) + m * (Real.exp (-lam*(2*mu-t)) / b) - 2*(Nn - m) ) := by
      rw [hGlogD, ha, hb]; ring
    rw [key]; apply mul_pos hlam
    have hane : a ≠ 0 := ne_of_gt hapos
    have hbne : b ≠ 0 := ne_of_gt hbpos
    have hEa : Real.exp (-lam*t) / a = 1/a - 1 := by
      have : Real.exp (-lam*t) = 1 - a := by rw [ha]; ring
      rw [this]; field_simp
    have hEb : Real.exp (-lam*(2*mu-t)) / b = 1/b - 1 := by
      have : Real.exp (-lam*(2*mu-t)) = 1 - b := by rw [hb]; ring
      rw [this]; field_simp
    rw [hEa, hEb]
    set EA : ℝ := Real.exp (lam*t) with hEA
    set EB : ℝ := Real.exp (lam*(2*mu-t)) with hEB
    have hEApos : 0 < EA := Real.exp_pos _
    have hEBpos : 0 < EB := Real.exp_pos _
    have hEA1 : 1 < EA := by rw [hEA, Real.one_lt_exp_iff]; nlinarith
    have hEB1 : 1 < EB := by rw [hEB, Real.one_lt_exp_iff]; nlinarith
    set α : ℝ := EA - 1 with hα
    set β : ℝ := EB - 1 with hβ
    have hαpos : 0 < α := by rw [hα]; linarith
    have hβpos : 0 < β := by rw [hβ]; linarith
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hβne : β ≠ 0 := ne_of_gt hβpos
    have ha_alt : a = α / EA := by
      rw [ha, hα, hEA]
      have he : Real.exp (-lam*t) = (Real.exp (lam*t))⁻¹ := by rw [← Real.exp_neg]; ring_nf
      rw [he]; field_simp
    have hb_alt : b = β / EB := by
      rw [hb, hβ, hEB]
      have he : Real.exp (-lam*(2*mu-t)) = (Real.exp (lam*(2*mu-t)))⁻¹ := by rw [← Real.exp_neg]; ring_nf
      rw [he]; field_simp
    have ha_eq : 1/a - 1 = 1/α := by rw [ha_alt]; field_simp; ring
    have hb_eq : 1/b - 1 = 1/β := by rw [hb_alt]; field_simp; ring
    rw [ha_eq, hb_eq]
    have hprod : EA * EB = Real.exp (2*lam*mu) := by rw [hEA, hEB, ← Real.exp_add]; ring_nf
    set Emu : ℝ := Real.exp (lam*mu) with hEmu
    have hEmupos : 0 < Emu := Real.exp_pos _
    have hEmu2 : Emu * Emu = Real.exp (2*lam*mu) := by rw [hEmu, ← Real.exp_add]; ring_nf
    have hamgm : 2 * Emu ≤ EA + EB := by
      have hEAEB : EA * EB = Emu * Emu := by rw [hprod, hEmu2]
      nlinarith [sq_nonneg (EA - EB), mul_pos hEApos hEBpos, hEAEB, hEmupos]
    have hαβpos : 0 < α * β := mul_pos hαpos hβpos
    have hαβ_eq : α * β = Emu * Emu - (EA + EB) + 1 := by rw [hEmu2, ← hprod, hα, hβ]; ring
    have hnum : 0 < m * β + m * α - 2*(Nn - m) * (α * β) := by
      rw [hαβ_eq]
      have hmab : m * β + m * α = m * (EA + EB - 2) := by rw [hα, hβ]; ring
      rw [hmab]
      have hEmu1 : 1 < Emu := by rw [hEmu, Real.one_lt_exp_iff]; positivity
      have hfac : (Emu - 1) * ((Nn - m) * Emu - Nn) < 0 := by
        apply mul_neg_of_pos_of_neg
        · linarith
        · linarith [hcond]
      nlinarith [hamgm, hfac, mul_pos (show (0:ℝ) < 2*(Nn-m) by linarith) hEmupos, hNm, hEmupos]
    have heq : m * (1/α) + m * (1/β) - 2*(Nn-m)
          = (m * β + m * α - 2*(Nn-m)*(α*β)) / (α*β) := by field_simp
    rw [heq]; exact div_pos hnum hαβpos
  exact ⟨hderiv, hpos⟩
