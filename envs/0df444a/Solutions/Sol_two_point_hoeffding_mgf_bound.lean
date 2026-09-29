-- Prove2me | solution 1 for two_point_hoeffding_mgf_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T00:20:46.712935+00:00
-- url     : https://prove2.me/submissions/2aa385ec-c8a9-43ab-b1f8-bcd46fa2241e

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue

set_option maxHeartbeats 1000000

open scoped BigOperators

/-- **Two-point Hoeffding MGF inequality** (Hoeffding 1963; BLM, *Concentration
Inequalities*, OUP 2013, Lemma 2.2).

For a real number `p ∈ [0,1]` and reals `a b`, the two-point convex combination of
exponentials is bounded by the exponential of the mean plus a Gaussian-type term:
`p·e^a + (1-p)·e^b ≤ exp(p·a + (1-p)·b + (a-b)²/8)`.

Equivalently, for a two-point random variable taking value `a` with probability `p`
and `b` with probability `1-p`, the MGF is sub-Gaussian with variance proxy
`(a-b)²/4`. -/
theorem solution (p a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * Real.exp a + (1 - p) * Real.exp b ≤
      Real.exp (p * a + (1 - p) * b + (a - b) ^ 2 / 8) := by
  -- The denominator `D t = (1 - p) + p * exp t` is strictly positive for all `t`.
  have hD : ∀ t : ℝ, 0 < (1 - p) + p * Real.exp t := by
    intro t
    rcases eq_or_lt_of_le hp0 with h | h
    · -- p = 0
      simp [← h]
    · -- 0 < p
      have : 0 < p * Real.exp t := mul_pos h (Real.exp_pos t)
      linarith [show (0:ℝ) ≤ 1 - p from by linarith]
  -- φ t = log(D t) - p * t.  We prove φ s ≤ s²/8 where s = a - b, via the
  -- auxiliary ψ t = t²/8 - φ t which has a global minimum 0 at t = 0.
  set φ : ℝ → ℝ := fun t => Real.log ((1 - p) + p * Real.exp t) - p * t with hφ
  -- Derivative of φ at any t is u t - p where u t = p*exp t / D t.
  have hφderiv : ∀ t : ℝ,
      HasDerivAt φ (p * Real.exp t / ((1 - p) + p * Real.exp t) - p) t := by
    intro t
    have hDpos := hD t
    have hDne : ((1 - p) + p * Real.exp t) ≠ 0 := ne_of_gt hDpos
    -- D t has derivative p * exp t
    have hDder : HasDerivAt (fun t => (1 - p) + p * Real.exp t) (p * Real.exp t) t := by
      have h1 : HasDerivAt (fun t : ℝ => p * Real.exp t) (p * Real.exp t) t := by
        have := (Real.hasDerivAt_exp t).const_mul p
        simpa using this
      exact h1.const_add (1 - p)
    -- log (D t) has derivative (p exp t) / D t
    have hlog : HasDerivAt (fun t => Real.log ((1 - p) + p * Real.exp t))
        (p * Real.exp t / ((1 - p) + p * Real.exp t)) t := by
      have := hDder.log hDne
      simpa using this
    -- p * t has derivative p
    have hpt : HasDerivAt (fun t : ℝ => p * t) p t := by
      simpa using (hasDerivAt_id t).const_mul p
    rw [hφ]
    exact hlog.fun_sub hpt
  -- Auxiliary g t = t/4 - φ' t = t/4 - (u t - p).  We show g is monotone (g' ≥ 0)
  -- and g 0 = 0, hence g ≥ 0 on [0,∞) and g ≤ 0 on (-∞,0].
  set g : ℝ → ℝ := fun t => t / 4 - (p * Real.exp t / ((1 - p) + p * Real.exp t) - p) with hg
  -- u t := p exp t / D t,  u' = u (1 - u).  Derivative of g is 1/4 - u(1-u) ≥ 0.
  have hgderiv : ∀ t : ℝ, HasDerivAt g
      (1/4 - (p * Real.exp t * ((1 - p) + p * Real.exp t)
        - p * Real.exp t * (p * Real.exp t))
        / (((1 - p) + p * Real.exp t)) ^ 2) t := by
    intro t
    have hDpos := hD t
    have hDne : ((1 - p) + p * Real.exp t) ≠ 0 := ne_of_gt hDpos
    -- numerator N t = p * exp t,  N' = p exp t
    have hN : HasDerivAt (fun t : ℝ => p * Real.exp t) (p * Real.exp t) t := by
      simpa using (Real.hasDerivAt_exp t).const_mul p
    -- denom D t,  D' = p exp t
    have hDder : HasDerivAt (fun t => (1 - p) + p * Real.exp t) (p * Real.exp t) t := by
      have h1 : HasDerivAt (fun t : ℝ => p * Real.exp t) (p * Real.exp t) t := by
        simpa using (Real.hasDerivAt_exp t).const_mul p
      exact h1.const_add (1 - p)
    -- u = N / D
    have hu : HasDerivAt (fun t => p * Real.exp t / ((1 - p) + p * Real.exp t))
        ((p * Real.exp t * ((1 - p) + p * Real.exp t)
            - p * Real.exp t * (p * Real.exp t))
          / (((1 - p) + p * Real.exp t)) ^ 2) t := by
      exact hN.fun_div hDder hDne
    -- t/4 has derivative 1/4
    have ht4 : HasDerivAt (fun t : ℝ => t / 4) (1/4) t := by
      simpa using (hasDerivAt_id t).div_const 4
    -- (u t - p) has derivative u'
    have huP := hu.sub_const p
    rw [hg]
    exact ht4.fun_sub huP
  -- deriv g t ≥ 0 everywhere: 1/4 ≥ u (1 - u).
  have hgderiv_nonneg : ∀ t : ℝ, 0 ≤
      (1/4 - (p * Real.exp t * ((1 - p) + p * Real.exp t)
        - p * Real.exp t * (p * Real.exp t))
        / (((1 - p) + p * Real.exp t)) ^ 2) := by
    intro t
    have hDpos := hD t
    set D := (1 - p) + p * Real.exp t with hDdef
    set N := p * Real.exp t with hNdef
    have hN0 : 0 ≤ N := by
      have := mul_nonneg hp0 (le_of_lt (Real.exp_pos t)); simpa [hNdef] using this
    have hND : N ≤ D := by
      -- D - N = 1 - p ≥ 0
      have : D - N = 1 - p := by simp only [hDdef, hNdef]; ring
      have h1p : 0 ≤ 1 - p := by linarith
      linarith
    have hD2 : 0 < D ^ 2 := by positivity
    rw [sub_nonneg, div_le_iff₀ hD2]
    -- need N*D - N*N ≤ (1/4) * D^2, i.e. N(D-N) ≤ D²/4.  Since N(D-N) ≤ D²/4 ⟺ (D-2N)²≥0.
    nlinarith [sq_nonneg (D - 2*N), hDpos, hN0, hND]
  -- g is monotone everywhere
  have hg_mono : Monotone g := by
    apply monotone_of_deriv_nonneg
    · intro t; exact (hgderiv t).differentiableAt
    · intro t; rw [(hgderiv t).deriv]; exact hgderiv_nonneg t
  -- g 0 = 0
  have hg0 : g 0 = 0 := by
    simp only [hg]
    rw [Real.exp_zero]
    have : (1 - p) + p * 1 = 1 := by ring
    rw [this]
    simp
  -- Now ψ t = t²/8 - φ t has deriv g, ψ 0 = 0; show ψ s ≥ 0.
  set ψ : ℝ → ℝ := fun t => t ^ 2 / 8 - φ t with hψ
  have hψderiv : ∀ t : ℝ, HasDerivAt ψ (g t) t := by
    intro t
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 8) (t / 4) t := by
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      exact (h2.div_const 8).congr_deriv (by ring)
    rw [hψ, hg]
    exact hsq.fun_sub (hφderiv t)
  have hψ0 : ψ 0 = 0 := by
    simp only [hψ, hφ]
    rw [Real.exp_zero]
    have h1 : (1 - p) + p * 1 = 1 := by ring
    rw [h1, Real.log_one]
    ring
  -- g t ≥ 0 for t ≥ 0, g t ≤ 0 for t ≤ 0.
  have hg_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t := by
    intro t ht; calc (0:ℝ) = g 0 := hg0.symm
      _ ≤ g t := hg_mono ht
  have hg_nonpos : ∀ t : ℝ, t ≤ 0 → g t ≤ 0 := by
    intro t ht; calc g t ≤ g 0 := hg_mono ht
      _ = 0 := hg0
  -- ψ is monotone on [0,∞): deriv = g ≥ 0.
  have hψ_mono_pos : MonotoneOn ψ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hψderiv t).continuousAt.continuousWithinAt
    · intro t _; exact (hψderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hψderiv t).deriv]
      have htpos : 0 ≤ t := by simpa using interior_subset ht
      exact hg_nonneg t htpos
  -- ψ is antitone on (-∞,0]: deriv = g ≤ 0.
  have hψ_anti_neg : AntitoneOn ψ (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · exact fun t _ => (hψderiv t).continuousAt.continuousWithinAt
    · intro t _; exact (hψderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hψderiv t).deriv]
      have htneg : t ≤ 0 := by simpa using interior_subset ht
      exact hg_nonpos t htneg
  -- Hence ψ s ≥ ψ 0 = 0 for every s.
  have hψ_nonneg : ∀ s : ℝ, 0 ≤ ψ s := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · have := hψ_mono_pos (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
      rw [hψ0] at this; exact this
    · have := hψ_anti_neg (Set.mem_Iic.mpr (le_of_lt hs)) (Set.mem_Iic.mpr le_rfl) (le_of_lt hs)
      rw [hψ0] at this; exact this
  -- So φ s ≤ s²/8 for every s, in particular for s = a - b.
  have hkey : φ (a - b) ≤ (a - b) ^ 2 / 8 := by
    have := hψ_nonneg (a - b)
    simp only [hψ] at this
    linarith
  -- Translate back: log(p·e^a+(1-p)·e^b) ≤ p·a+(1-p)·b + (a-b)²/8.
  -- Factor e^b: p·e^a+(1-p)·e^b = e^b · ((1-p) + p·e^(a-b)).
  have hpos : 0 < p * Real.exp a + (1 - p) * Real.exp b := by
    rcases eq_or_lt_of_le hp0 with h | h
    · have : (1 - p) * Real.exp b = Real.exp b := by rw [← h]; ring
      rw [← h]; simp [Real.exp_pos]
    · have h1 : 0 < p * Real.exp a := mul_pos h (Real.exp_pos a)
      have h2 : 0 ≤ (1 - p) * Real.exp b :=
        mul_nonneg (by linarith) (le_of_lt (Real.exp_pos b))
      linarith
  -- It suffices to show log of LHS ≤ the exponent argument.
  rw [← Real.exp_log hpos]
  rw [Real.exp_le_exp]
  -- log(p·e^a+(1-p)·e^b) = b + log((1-p) + p·e^(a-b))
  have hfactor : p * Real.exp a + (1 - p) * Real.exp b
      = Real.exp b * ((1 - p) + p * Real.exp (a - b)) := by
    rw [Real.exp_sub]
    field_simp
    ring
  rw [hfactor]
  rw [Real.log_mul (ne_of_gt (Real.exp_pos b)) (ne_of_gt (hD (a - b)))]
  rw [Real.log_exp]
  -- Goal: b + log((1-p)+p e^(a-b)) ≤ p a + (1-p) b + (a-b)²/8
  -- and φ(a-b) = log((1-p)+p e^(a-b)) - p (a-b).
  have hφval : φ (a - b) = Real.log ((1 - p) + p * Real.exp (a - b)) - p * (a - b) := rfl
  rw [hφval] at hkey
  nlinarith [hkey]
