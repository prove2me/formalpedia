-- Prove2me | solution 1 for phi_single_turning_point
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T20:16:54.486773+00:00
-- url     : https://prove2.me/submissions/c16f85f5-a64e-4084-a763-7913047c57c0

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open Set

/-- The waiting-time log-density derivative `G'(s) = m·λ·e^{-λs}/(1-e^{-λs}) - (Nn-m)·λ`. -/
noncomputable def GlogD (lam m Nn : ℝ) (s : ℝ) : ℝ :=
  m * (lam * Real.exp (-lam * s) / (1 - Real.exp (-lam * s))) - (Nn - m) * lam

/-- The log-density `G(t) = m·log(1-e^{-λt}) - (Nn-m)·λt`. -/
noncomputable def Glog (lam m Nn : ℝ) (t : ℝ) : ℝ :=
  m * Real.log (1 - Real.exp (-lam * t)) - (Nn - m) * (lam * t)

theorem Glog_hasDeriv (lam m Nn : ℝ) (s : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    HasDerivAt (Glog lam m Nn) (GlogD lam m Nn s) s := by
  unfold Glog GlogD
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
  have hd := (hlog.const_mul m).sub hlin
  exact hd

/-- φ(t) = G(t) - G(2µ-t). -/
theorem phi_hasDeriv (lam m Nn mu : ℝ) (t : ℝ) (ht0 : 0 < t) (htmu : t < mu) (hlam : 0 < lam) :
    HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
      (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t := by
  have hpt : (0:ℝ) < 2*mu - t := by linarith
  have h1 := Glog_hasDeriv lam m Nn t ht0 hlam
  have hinner : HasDerivAt (fun y => 2*mu - y) (-1 : ℝ) t := by
    have := (hasDerivAt_id t).const_sub (2*mu); simpa using this
  have h2 := Glog_hasDeriv lam m Nn (2*mu - t) hpt hlam
  have hcomp : HasDerivAt (fun y => Glog lam m Nn (2*mu - y)) (GlogD lam m Nn (2*mu - t) * (-1)) t :=
    h2.comp t hinner
  have hd := h1.sub hcomp
  have hval : GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)
      = GlogD lam m Nn t - GlogD lam m Nn (2*mu - t) * (-1) := by ring
  rw [hval]
  exact hd

/-- **Sign of φ' equals sign of the quadratic `Q(e^{λt})`.**  Concretely
`φ'(t) = (λ / (α·β·u)) · Q(u)` with `u = e^{λt}`, `α = e^{λt}-1`, `β = e^{λ(2µ-t)}-1`,
`A = e^{2λµ}`, and `Q(u) = (2Nn-m)u² - 2(Nn+(Nn-m)A)u + A(2Nn-m)`.  Since `λ, α, β, u > 0`,
`sign(φ'(t)) = sign(Q(e^{λt}))`. -/
theorem phiD_eq (lam m Nn mu : ℝ) (t : ℝ) (ht0 : 0 < t) (htmu : t < mu) (hlam : 0 < lam) :
    (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t))
      = (lam / ((Real.exp (lam*t) - 1) * (Real.exp (lam*(2*mu-t)) - 1) * Real.exp (lam*t)))
        * ((2*Nn - m) * (Real.exp (lam*t))^2
           - 2*(Nn + (Nn - m)*Real.exp (2*lam*mu)) * Real.exp (lam*t)
           + Real.exp (2*lam*mu) * (2*Nn - m)) := by
  have hlt : Real.exp (-lam * t) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hlt2 : Real.exp (-lam * (2*mu - t)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  set a : ℝ := 1 - Real.exp (-lam * t) with ha
  set b : ℝ := 1 - Real.exp (-lam * (2*mu - t)) with hb
  have hapos : 0 < a := by rw [ha]; linarith
  have hbpos : 0 < b := by rw [hb]; linarith
  have hane : a ≠ 0 := ne_of_gt hapos
  have hbne : b ≠ 0 := ne_of_gt hbpos
  -- express exponentials
  set EA : ℝ := Real.exp (lam*t) with hEA
  set EB : ℝ := Real.exp (lam*(2*mu-t)) with hEB
  have hEApos : 0 < EA := Real.exp_pos _
  have hEBpos : 0 < EB := Real.exp_pos _
  have hEA1 : 1 < EA := by rw [hEA, Real.one_lt_exp_iff]; nlinarith
  have hEB1 : 1 < EB := by rw [hEB, Real.one_lt_exp_iff]; nlinarith
  have heA : Real.exp (-lam*t) = EA⁻¹ := by rw [hEA, ← Real.exp_neg]; ring_nf
  have heB : Real.exp (-lam*(2*mu-t)) = EB⁻¹ := by rw [hEB, ← Real.exp_neg]; ring_nf
  have haEA : a = (EA - 1)/EA := by rw [ha, heA]; field_simp
  have hbEB : b = (EB - 1)/EB := by rw [hb, heB]; field_simp
  have hαpos : 0 < EA - 1 := by linarith
  have hβpos : 0 < EB - 1 := by linarith
  have hprod : EA * EB = Real.exp (2*lam*mu) := by rw [hEA, hEB, ← Real.exp_add]; ring_nf
  -- GlogD t = m*(lam*exp(-lt)/a) - (Nn-m)*lam ; rewrite exp(-lt)/a
  have hGt : GlogD lam m Nn t = m * (lam * (EA⁻¹ / a)) - (Nn - m) * lam := by
    unfold GlogD; rw [← ha, heA]; ring
  have hGt2 : GlogD lam m Nn (2*mu - t) = m * (lam * (EB⁻¹ / b)) - (Nn - m) * lam := by
    unfold GlogD; rw [show 2*mu - t = 2*mu - t from rfl]
    have : (1 - Real.exp (-lam * (2*mu - t))) = b := by rw [hb]
    rw [this, heB]; ring
  rw [hGt, hGt2]
  rw [haEA, hbEB]
  have hEAne : EA ≠ 0 := ne_of_gt hEApos
  have hEBne : EB ≠ 0 := ne_of_gt hEBpos
  have hα : EA - 1 ≠ 0 := ne_of_gt hαpos
  have hβ : EB - 1 ≠ 0 := ne_of_gt hβpos
  rw [← hprod]
  field_simp
  ring

/-- The quadratic `Qp A u = (2Nn-m)u² - 2(Nn+(Nn-m)A)u + A(2Nn-m)`. -/
noncomputable def Qp (m Nn A u : ℝ) : ℝ :=
  (2*Nn - m) * u^2 - 2*(Nn + (Nn - m)*A) * u + A * (2*Nn - m)

theorem Qp_at_one (m Nn A : ℝ) : Qp m Nn A 1 = m * (A - 1) := by
  unfold Qp; ring

theorem Qp_at_sqrtA (m Nn s : ℝ) : Qp m Nn (s^2) s = -2 * s * (s - 1) * ((Nn - m)*s - Nn) := by
  unfold Qp; ring

/-- `Qp` is strictly decreasing on `[1, s]` when `s ≤ vertex`, which holds under the mean
condition. We prove it directly: for `1 ≤ x < y ≤ s`, `Qp x > Qp y`. -/
theorem Qp_strictAnti (m Nn A s : ℝ) (hs1 : 1 < s) (hA : A = s^2)
    (hlead : 0 < 2*Nn - m) (hvert : s * (2*Nn - m) < Nn + (Nn - m)*A) :
    StrictAntiOn (Qp m Nn A) (Set.Icc 1 s) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  unfold Qp
  have hxs : x ≤ s := hx.2
  have hys : y ≤ s := hy.2
  have h1x : 1 ≤ x := hx.1
  -- Qp x - Qp y = (2Nn-m)(x²-y²) - 2(Nn+(Nn-m)A)(x-y)
  --            = (x-y)[(2Nn-m)(x+y) - 2(Nn+(Nn-m)A)]
  -- x-y<0, and (2Nn-m)(x+y) ≤ (2Nn-m)(2s) = 2s(2Nn-m) < 2(Nn+(Nn-m)A), so bracket<0, product>0
  nlinarith [hlead, hvert, hxy, h1x, hxs, hys, mul_pos hlead (show (0:ℝ) < y - x by linarith)]

/-- Under the mean condition `Nn < (Nn-m)·s` (with `s = e^{λµ} > 1`, `0 < m < Nn`), the point
`s` lies strictly left of the parabola vertex: `s·(2Nn-m) < Nn + (Nn-m)·s²`. -/
theorem vertex_cond (m Nn s : ℝ) (hm : 0 < m) (hmN : m < Nn) (hs1 : 1 < s)
    (hmean : Nn < (Nn - m) * s) :
    s * (2*Nn - m) < Nn + (Nn - m) * s^2 := by
  have hNm : 0 < Nn - m := by linarith
  -- (Nn-m)s² - (2Nn-m)s + Nn = (Nn-m)(s-1)(s - Nn/(Nn-m)); both factors > 0
  -- (Nn-m)(s-1) > 0 ; (Nn-m)s - Nn > 0 from hmean
  nlinarith [mul_pos (mul_pos hNm (show (0:ℝ) < s - 1 by linarith)) (show (0:ℝ) < (Nn - m)*s - Nn by linarith)]

/-- **Siegel 2001, Thm 2.2 / §2.1.1 — the φ' single-turning-point step (failure-reversal regime).**
For the waiting-time log-density `G(t) = m·log(1-e^{-λt}) - (Nn-m)·λt` and the symmetrized
log-ratio `φ(t) = G(t) - G(2µ-t)`, under the *mean* condition `Nn < (Nn-m)·e^{λµ}`
(equivalently `e^{λµ} > Nn/(Nn-m)`, which is exactly the regime where `µ = E[T]` sits ABOVE
the threshold — the failure-reversed binomial), the derivative `φ'` is **positive then negative**:
there is a single interior maximum `a ∈ (0,µ)` with `φ'(t) > 0` for `t ∈ (0,a)` and `φ'(t) < 0`
for `t ∈ (a,µ)`.  This is the unimodality that drives Siegel's moustache argument in the
non-degenerate (binomial-median) case. -/
theorem phi_single_turning_point_aux
    (lam m Nn mu : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hmN : m < Nn) (hmu : 0 < mu)
    (hmean : Nn < (Nn - m) * Real.exp (lam * mu)) :
    ∃ a ∈ Ioo (0:ℝ) mu,
      (∀ t ∈ Ioo (0:ℝ) a,
        HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
          (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
        ∧ 0 < GlogD lam m Nn t + GlogD lam m Nn (2*mu - t))
      ∧ (∀ t ∈ Ioo a mu,
        HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
          (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
        ∧ GlogD lam m Nn t + GlogD lam m Nn (2*mu - t) < 0) := by
  set s : ℝ := Real.exp (lam * mu) with hs_def
  have hspos : 0 < s := Real.exp_pos _
  have hs1 : 1 < s := by rw [hs_def, Real.one_lt_exp_iff]; positivity
  set A : ℝ := Real.exp (2*lam*mu) with hA_def
  have hAs2 : A = s^2 := by
    rw [hA_def, hs_def, sq, ← Real.exp_add]; ring_nf
  have hlead : 0 < 2*Nn - m := by linarith
  have hNm : 0 < Nn - m := by linarith
  -- ψ(t) = Qp(e^{λt})
  set ψ : ℝ → ℝ := fun t => Qp m Nn A (Real.exp (lam*t)) with hψ_def
  -- e^{λ·} maps [0,µ] into [1,s] and is strictly mono
  have hexp_mono : StrictMonoOn (fun t => Real.exp (lam*t)) (Icc 0 mu) := by
    intro x _ y _ hxy
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hexp_mem : ∀ t ∈ Icc (0:ℝ) mu, Real.exp (lam*t) ∈ Icc (1:ℝ) s := by
    intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    constructor
    · rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [ht.1])
    · rw [hs_def]; exact Real.exp_le_exp.mpr (by nlinarith [ht.2])
  -- Qp strictly anti on [1,s]
  have hvert : s * (2*Nn - m) < Nn + (Nn - m)*A := by
    rw [hAs2]; exact vertex_cond m Nn s hm hmN hs1 hmean
  have hQanti := Qp_strictAnti m Nn A s hs1 hAs2 hlead hvert
  -- ψ strictly anti on [0,µ]
  have hψanti : StrictAntiOn ψ (Icc 0 mu) := by
    intro x hx y hy hxy
    have hex := hexp_mem x hx
    have hey := hexp_mem y hy
    have : Real.exp (lam*x) < Real.exp (lam*y) := hexp_mono hx hy hxy
    exact hQanti hex hey this
  -- ψ continuous
  have hψcont : ContinuousOn ψ (Icc 0 mu) := by
    have : Continuous ψ := by
      rw [hψ_def]
      have hQc : Continuous (Qp m Nn A) := by unfold Qp; fun_prop
      exact hQc.comp (by fun_prop)
    exact this.continuousOn
  -- ψ(0) = Qp(1) > 0 ; ψ(µ) = Qp(s) < 0
  have hψ0 : 0 < ψ 0 := by
    have : ψ 0 = m * (A - 1) := by
      rw [hψ_def]; simp only [mul_zero, Real.exp_zero]; exact Qp_at_one m Nn A
    rw [this]
    have hA1 : 1 < A := by rw [hAs2]; nlinarith [hs1]
    have : 0 < A - 1 := by linarith
    exact mul_pos hm this
  have hψμ : ψ mu < 0 := by
    have hval : ψ mu = -2 * s * (s - 1) * ((Nn - m)*s - Nn) := by
      show Qp m Nn A (Real.exp (lam*mu)) = _
      rw [← hs_def, hAs2]; exact Qp_at_sqrtA m Nn s
    rw [hval]
    have h1 : 0 < 2 * s * (s - 1) := by nlinarith [hspos, hs1]
    have h2 : 0 < (Nn - m)*s - Nn := by linarith [hmean]
    nlinarith [h1, h2]
  -- IVT: ∃ a ∈ (0,µ), ψ a = 0
  have hμpos : (0:ℝ) ≤ mu := hmu.le
  obtain ⟨a, ha_mem, ha_zero⟩ : ∃ a ∈ Ioo (0:ℝ) mu, ψ a = 0 := by
    have hcont' : ContinuousOn ψ (Icc 0 mu) := hψcont
    have hsign : (0:ℝ) ∈ Ioo (ψ mu) (ψ 0) := ⟨hψμ, hψ0⟩
    obtain ⟨a, ha, hva⟩ := intermediate_value_Ioo' hμpos hcont' hsign
    exact ⟨a, ha, hva⟩
  obtain ⟨ha0, haμ⟩ := ha_mem
  refine ⟨a, ⟨ha0, haμ⟩, ?_, ?_⟩
  · -- t ∈ (0,a): ψ t > ψ a = 0
    intro t ht
    obtain ⟨ht0, hta⟩ := ht
    have htμ : t < mu := lt_trans hta haμ
    have hψt_pos : 0 < ψ t := by
      have := hψanti (Set.mem_Icc.mpr ⟨ht0.le, htμ.le⟩) (Set.mem_Icc.mpr ⟨ha0.le, haμ.le⟩) hta
      rw [ha_zero] at this; linarith
    refine ⟨phi_hasDeriv lam m Nn mu t ht0 htμ hlam, ?_⟩
    -- φ'(t) = prefactor · ψ t, prefactor > 0
    rw [phiD_eq lam m Nn mu t ht0 htμ hlam]
    have hpre : 0 < lam / ((Real.exp (lam*t) - 1) * (Real.exp (lam*(2*mu-t)) - 1) * Real.exp (lam*t)) := by
      apply div_pos hlam
      have h1 : 0 < Real.exp (lam*t) - 1 := by
        have : 1 < Real.exp (lam*t) := by rw [Real.one_lt_exp_iff]; positivity
        linarith
      have h2 : 0 < Real.exp (lam*(2*mu-t)) - 1 := by
        have : 1 < Real.exp (lam*(2*mu-t)) := by rw [Real.one_lt_exp_iff]; nlinarith
        linarith
      positivity
    have hψeq : ((2*Nn - m) * (Real.exp (lam*t))^2
           - 2*(Nn + (Nn - m)*Real.exp (2*lam*mu)) * Real.exp (lam*t)
           + Real.exp (2*lam*mu) * (2*Nn - m)) = ψ t := by
      rw [hψ_def]; unfold Qp; rw [hA_def]
    rw [hψeq]; exact mul_pos hpre hψt_pos
  · -- t ∈ (a,µ): ψ t < ψ a = 0
    intro t ht
    obtain ⟨hat, htμ⟩ := ht
    have ht0 : 0 < t := lt_trans ha0 hat
    have hψt_neg : ψ t < 0 := by
      have := hψanti (Set.mem_Icc.mpr ⟨ha0.le, haμ.le⟩) (Set.mem_Icc.mpr ⟨ht0.le, htμ.le⟩) hat
      rw [ha_zero] at this; linarith
    refine ⟨phi_hasDeriv lam m Nn mu t ht0 htμ hlam, ?_⟩
    rw [phiD_eq lam m Nn mu t ht0 htμ hlam]
    have hpre : 0 < lam / ((Real.exp (lam*t) - 1) * (Real.exp (lam*(2*mu-t)) - 1) * Real.exp (lam*t)) := by
      apply div_pos hlam
      have h1 : 0 < Real.exp (lam*t) - 1 := by
        have : 1 < Real.exp (lam*t) := by rw [Real.one_lt_exp_iff]; positivity
        linarith
      have h2 : 0 < Real.exp (lam*(2*mu-t)) - 1 := by
        have : 1 < Real.exp (lam*(2*mu-t)) := by rw [Real.one_lt_exp_iff]; nlinarith
        linarith
      positivity
    have hψeq : ((2*Nn - m) * (Real.exp (lam*t))^2
           - 2*(Nn + (Nn - m)*Real.exp (2*lam*mu)) * Real.exp (lam*t)
           + Real.exp (2*lam*mu) * (2*Nn - m)) = ψ t := by
      rw [hψ_def]; unfold Qp; rw [hA_def]
    rw [hψeq]
    have := mul_neg_of_pos_of_neg hpre hψt_neg
    linarith [this]


theorem solution (lam m Nn mu : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hmN : m < Nn) (hmu : 0 < mu) (hmean : Nn < (Nn - m) * Real.exp (lam * mu)) : ∃ a ∈ Set.Ioo (0:ℝ) mu, (∀ t ∈ Set.Ioo (0:ℝ) a, HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y)) - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y)))) (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) t ∧ 0 < (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam)))) ∧ (∀ t ∈ Set.Ioo a mu, HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y)) - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y)))) (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) t ∧ (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) < 0) := by
  exact phi_single_turning_point_aux lam m Nn mu hlam hm hmN hmu hmean
