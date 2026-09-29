-- Prove2me | solution 1 for scalar_centered_sampling_qnorm_rosenthal_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T02:44:52.701418+00:00
-- url     : https://prove2.me/submissions/fac29f89-d88a-4043-9f3c-bb4fee69d7b0

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_centered_sampling_coefficient_bernstein_mgf
import Theorems.Thm_bernoulli_moment_from_two_sided_mgf
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

namespace ProveAA

variable {n₁ n₂ : ℕ}

/-- -Coeff Ω = Coeff of -B. -/
theorem coeff_neg (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Om : Finset (Fin n₁ × Fin n₂)) :
    matrixEntrySum (centeredSamplingFluctuation Om p (-B)) =
      -(matrixEntrySum (centeredSamplingFluctuation Om p B)) := by
  unfold matrixEntrySum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w _
  show p⁻¹ * ((samplingProjection Om (-B)) w.1 w.2 - p * (-B) w.1 w.2)
      = -(p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2))
  by_cases h : (w.1, w.2) ∈ Om <;>
    simp [samplingProjection, Matrix.neg_apply, h] <;> ring

theorem entrySup_neg (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    entrySupNorm (-B) = entrySupNorm B := by
  unfold entrySupNorm; simp only [Matrix.neg_apply, abs_neg]

theorem frobSq_neg (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNormSq (-B) = frobeniusNormSq B := by
  unfold frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.neg_apply]; ring

theorem bound_step (q p V E frob : ℝ) (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hV : 0 < V) (hE : 0 < E) (hfrob : 0 ≤ frob) (hVfrob : V ≤ frob^2 / p) :
    2 * (q / (Real.exp 1 * (min (Real.sqrt (q/(2*V)) ) (p/E)))) ^ q
        * Real.exp (min (Real.sqrt (q/(2*V))) (p/E)^2 * V) ≤
      (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
  set lam := min (Real.sqrt (q/(2*V))) (p/E) with hlamdef
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hsqrtpos : 0 < Real.sqrt (q/(2*V)) := Real.sqrt_pos.mpr (by positivity)
  have hpEpos : 0 < p/E := by positivity
  have hlampos : 0 < lam := lt_min hsqrtpos hpEpos
  have hlamA : lam ≤ Real.sqrt (q/(2*V)) := min_le_left _ _
  have hlamB : lam ≤ p/E := min_le_right _ _
  have hlam2V : lam^2 * V ≤ q/2 := by
    have h1 : lam^2 ≤ q/(2*V) := by
      have hh := Real.sq_sqrt (show (0:ℝ) ≤ q/(2*V) by positivity)
      nlinarith [hlamA, hlampos, Real.sqrt_nonneg (q/(2*V)), hh,
        mul_le_mul hlamA hlamA hlampos.le (Real.sqrt_nonneg _)]
    have heq : (q/(2*V)) * V = q/2 := by
      rw [div_mul_eq_mul_div, mul_comm 2 V, ← div_div, mul_div_assoc, div_self (ne_of_gt hV), mul_one]
    have : lam^2 * V ≤ (q/(2*V)) * V := mul_le_mul_of_nonneg_right h1 hV.le
    rw [heq] at this; linarith [this]
  have hexp : Real.exp (lam^2 * V) ≤ Real.exp (q/2) := Real.exp_le_exp.mpr hlam2V
  -- q/lam ≤ √(2Vq) + (q/p)·E
  have hqlam : q / lam ≤ Real.sqrt (2*V*q) + (q/p) * E := by
    rw [div_le_iff₀ hlampos]
    rcases le_total (Real.sqrt (q/(2*V))) (p/E) with hcase | hcase
    · have hl : lam = Real.sqrt (q/(2*V)) := by rw [hlamdef, min_eq_left hcase]
      rw [hl]
      have hsq : Real.sqrt (2*V*q) * Real.sqrt (q/(2*V)) = q := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show (2*V*q) * (q/(2*V)) = q^2 by field_simp]
        rw [Real.sqrt_sq hqpos.le]
      have hrest : 0 ≤ (q/p) * E * Real.sqrt (q/(2*V)) := by positivity
      nlinarith [hsq, hrest]
    · have hl : lam = p/E := by rw [hlamdef, min_eq_right hcase]
      rw [hl]
      have hqpE : (q/p) * E * (p/E) = q := by field_simp
      have hrest : 0 ≤ Real.sqrt (2*V*q) * (p/E) := by positivity
      nlinarith [hqpE, hrest]
  have hsqrt2Vq : Real.sqrt (2*V*q) ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) := by
    have hrw : Real.sqrt 2 * (Real.sqrt (q/p) * frob) = Real.sqrt (2 * (q/p) * frob^2) := by
      rw [show (2 * (q/p) * frob^2) = 2 * ((q/p) * frob^2) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [Real.sqrt_mul (div_nonneg hqpos.le hp0.le), Real.sqrt_sq hfrob]
    rw [hrw]
    apply Real.sqrt_le_sqrt
    have hVq : V * q ≤ (frob^2/p) * q := mul_le_mul_of_nonneg_right hVfrob hqpos.le
    have : (frob^2/p) * q = 2 * (q/p) * frob^2 / 2 := by ring
    nlinarith [hVq, hqpos]
  have hJ : q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + (q/p) * E := by
    linarith [hqlam, hsqrt2Vq]
  -- merge exp(q/2) into the power base.
  have hmerge : (q / (Real.exp 1 * lam)) ^ q * Real.exp (q/2)
      = (q / (lam * Real.exp (1/2))) ^ q := by
    have he2 : Real.exp (q/2) = (Real.exp (1/2)) ^ q := by rw [← Real.exp_mul]; ring_nf
    rw [he2, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    have hexp1 : Real.exp 1 = Real.exp (1/2) * Real.exp (1/2) := by rw [← Real.exp_add]; norm_num
    rw [hexp1]; field_simp
  -- step: 2 A^q exp(lam²V) ≤ 2 A^q exp(q/2) = 2 (q/(lam exp½))^q
  have hstep1 : 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
      ≤ 2 * (q / (lam * Real.exp (1/2))) ^ q := by
    have h := mul_le_mul_of_nonneg_left hexp
      (show (0:ℝ) ≤ 2 * (q / (Real.exp 1 * lam)) ^ q by positivity)
    calc 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
        = (2 * (q / (Real.exp 1 * lam)) ^ q) * Real.exp (lam^2 * V) := by ring
      _ ≤ (2 * (q / (Real.exp 1 * lam)) ^ q) * Real.exp (q/2) := h
      _ = 2 * ((q / (Real.exp 1 * lam)) ^ q * Real.exp (q/2)) := by ring
      _ = 2 * (q / (lam * Real.exp (1/2))) ^ q := by rw [hmerge]
  -- base bound: q/(lam exp½) ≤ √2(√(q/p)frob+(q/p)E)
  have hbase : q / (lam * Real.exp (1/2)) ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by
    have hexphalf : (1:ℝ) ≤ Real.exp (1/2) := Real.one_le_exp (by norm_num)
    have h1 : q / (lam * Real.exp (1/2)) ≤ q / lam := by
      rw [div_le_div_iff₀ (by positivity) hlampos]
      have : lam ≤ lam * Real.exp (1/2) := by nlinarith [hlampos, hexphalf]
      nlinarith [hqpos, hlampos, this]
    have hJ' : q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by
      have hsqrt2 : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      have hnn : 0 ≤ (q/p) * E := by positivity
      calc q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + (q/p) * E := hJ
        _ ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + Real.sqrt 2 * ((q/p) * E) := by nlinarith [hsqrt2, hnn]
        _ = Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by ring
    linarith [h1, hJ']
  -- raise to q-th power.
  have hJnn : 0 ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by positivity
  have hpow : (q / (lam * Real.exp (1/2))) ^ q ≤ (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q :=
    Real.rpow_le_rpow (by positivity) hbase hqpos.le
  -- 2 * (√2 J')^q ≤ (2√2 J')^q  where J'=(√(q/p)frob+(q/p)E)
  have hfinal : 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q
      ≤ (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
    rw [show (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E))
          = 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) by ring]
    rw [Real.mul_rpow (by norm_num) hJnn]
    have h2q : (2:ℝ) ≤ 2 ^ q := by
      calc (2:ℝ) = 2 ^ (1:ℝ) := by rw [Real.rpow_one]
        _ ≤ 2 ^ q := Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr hq
    have hbasenn : 0 ≤ (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q :=
      Real.rpow_nonneg hJnn q
    nlinarith [h2q, hbasenn]
  calc 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
      ≤ 2 * (q / (lam * Real.exp (1/2))) ^ q := hstep1
    _ ≤ 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
        apply mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := hfinal

end ProveAA

open ProveAA

set_option maxHeartbeats 1600000

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∀ q : ℕ, 1 ≤ q →
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (C *
                (Real.sqrt
                    ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q := by
  refine ⟨2 * Real.sqrt 2, by positivity, ?_⟩
  intro n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hent hfrob q hq1
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hnn : (0:ℝ) < (n₁:ℝ) * (n₂:ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hnn]; exact_mod_cast hmle
  have hentSnn : 0 ≤ entrySupNorm B := by
    unfold entrySupNorm
    refine Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hentS : 0 ≤ entryScale := le_trans hentSnn hent
  have hfrobS : 0 ≤ frobScale := le_trans (by unfold frobeniusNorm; positivity) hfrob
  -- nonneg of RHS base
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq1
  -- Rewrite the moment via hCoeff.
  have hmomeq : bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q)
      = bernoulliExpectation p (fun Omega =>
          |matrixEntrySum (centeredSamplingFluctuation Omega p B)| ^ q) := by
    unfold bernoulliExpectation
    apply Finset.sum_congr rfl; intro Om _; simp only []; rw [hCoeff Om]
  rw [hmomeq]
  -- Abbreviate Z.
  set Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Om => matrixEntrySum (centeredSamplingFluctuation Om p B) with hZ
  -- RHS is nonneg.
  have hRHSnn : (0:ℝ) ≤ 2 * Real.sqrt 2 *
      (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale) := by positivity
  -- Case split: degenerate (moment = 0) vs main.
  by_cases hdeg : p = 0 ∨ p = 1 ∨ frobeniusNormSq B = 0 ∨ entryScale = 0
  · -- moment = 0 ≤ RHS
    have hmom0 : bernoulliExpectation p (fun Om => |Z Om| ^ q) = 0 := by
      rcases hdeg with h | h | h | h
      · -- p = 0
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hz : Z Om = 0 := by
          rw [hZ, h]; unfold matrixEntrySum centeredSamplingFluctuation; simp [inv_zero]
        simp only [hz, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
      · -- p = 1 : weight 0 except univ; Z univ = 0
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        by_cases huniv : Om = Finset.univ
        · have hZ0 : Z Om = 0 := by
            rw [hZ, h, huniv]
            unfold matrixEntrySum
            refine Finset.sum_eq_zero (fun w _ => ?_)
            show (1:ℝ)⁻¹ *
                ((samplingProjection Finset.univ B) w.1 w.2 - (1:ℝ) * B w.1 w.2) = 0
            simp [samplingProjection]
          simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
        · have hw : bernoulliObservationWeight p Om = 0 := by
            rw [h]; unfold bernoulliObservationWeight
            have hcard : Om.card < Fintype.card (Fin n₁ × Fin n₂) := by
              rcases lt_or_eq_of_le (Finset.card_le_univ Om) with hlt | heq
              · simpa using hlt
              · exact absurd (Finset.card_eq_iff_eq_univ Om |>.mp (by simpa using heq)) huniv
            have hne : Fintype.card (Fin n₁ × Fin n₂) - Om.card ≠ 0 := by omega
            rw [one_pow, one_mul, show (1:ℝ)-1 = 0 by norm_num, zero_pow hne]
          rw [hw, zero_mul]
      · -- frobeniusNormSq B = 0 ⇒ B = 0 ⇒ Z = 0
        have hB0 : ∀ i j, B i j = 0 := by
          intro i j
          have hsum : ∀ a, ∀ b, B a b ^ 2 = 0 := by
            intro a b
            have hnn2 : ∀ a, ∀ b, (0:ℝ) ≤ B a b ^ 2 := fun a b => sq_nonneg _
            unfold frobeniusNormSq at h
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (B i j)))).mp h
            have h2 := this a (Finset.mem_univ a)
            exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (B a j))).mp h2 b (Finset.mem_univ b)
          have := hsum i j; nlinarith [this]
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hZ0 : Z Om = 0 := by
          rw [hZ]
          unfold matrixEntrySum
          refine Finset.sum_eq_zero (fun w _ => ?_)
          show p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2) = 0
          simp [samplingProjection, hB0]
        simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
      · -- entryScale = 0 ⇒ entrySupNorm B = 0 ⇒ B = 0 ⇒ Z = 0
        have hsup0 : entrySupNorm B ≤ 0 := h ▸ hent
        have hB0 : ∀ i j, B i j = 0 := by
          intro i j
          have hbdd2 : ∀ a : Fin n₁, BddAbove (Set.range (fun b : Fin n₂ => |B a b|)) :=
            fun a => Set.Finite.bddAbove (Set.finite_range _)
          have hbdd1 : BddAbove (Set.range (fun a : Fin n₁ => ⨆ b : Fin n₂, |B a b|)) :=
            Set.Finite.bddAbove (Set.finite_range _)
          have hle : |B i j| ≤ entrySupNorm B := by
            unfold entrySupNorm
            exact le_trans (le_ciSup (hbdd2 i) j) (le_ciSup hbdd1 i)
          have : |B i j| ≤ 0 := le_trans hle hsup0
          have := abs_nonpos_iff.mp this; exact this
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hZ0 : Z Om = 0 := by
          rw [hZ]
          unfold matrixEntrySum
          refine Finset.sum_eq_zero (fun w _ => ?_)
          show p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2) = 0
          simp [samplingProjection, hB0]
        simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
    rw [hmom0]; positivity
  · -- MAIN: p∈(0,1), frobeniusNormSq B>0, entryScale>0.
    push_neg at hdeg
    obtain ⟨hpne0, hpne1, hFne, hEne⟩ := hdeg
    have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpne0)
    have hEpos : 0 < entryScale := lt_of_le_of_ne hentS (Ne.symm hEne)
    have hFpos : 0 < frobeniusNormSq B := lt_of_le_of_ne (by unfold frobeniusNormSq; positivity) (Ne.symm hFne)
    set V : ℝ := (1 - p) / p * frobeniusNormSq B with hVdef
    have hppos1 : p < 1 := lt_of_le_of_ne hp1 hpne1
    have h1mp0 : 0 < 1 - p := by linarith
    have hVpos : 0 < V := by rw [hVdef]; positivity
    -- frobScale > 0 (else frobeniusNormSq B ≤ frobScale^2 = 0)
    have hFle : frobeniusNormSq B ≤ frobScale ^ 2 := by
      have hsqle : Real.sqrt (frobeniusNormSq B) ≤ frobScale := by
        have := hfrob; unfold frobeniusNorm at this; exact this
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ frobeniusNormSq B by unfold frobeniusNormSq; positivity),
        hsqle, hfrobS, Real.sqrt_nonneg (frobeniusNormSq B)]
    have hfrobSpos : 0 < frobScale := by
      rcases lt_or_eq_of_le hfrobS with hlt | heq
      · exact hlt
      · exfalso; rw [← heq] at hFle; simp at hFle; linarith [hFpos, hFle]
    -- V ≤ frobScale^2 / p
    have hVfrob : V ≤ frobScale ^ 2 / p := by
      rw [hVdef]
      have h1mp : (1 - p) ≤ 1 := by linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hppos hppos]
      have h1 : (1-p)*frobeniusNormSq B ≤ frobeniusNormSq B := by nlinarith [h1mp, h1mp0, hFpos.le]
      have h2 : (1-p)*frobeniusNormSq B ≤ frobScale^2 := le_trans h1 hFle
      nlinarith [h2, hppos.le]
    -- choose lam = min(√(q/(2V)), p/entryScale).
    set lam : ℝ := min (Real.sqrt ((q:ℝ)/(2*V))) (p/entryScale) with hlam
    have hsqrtpos : 0 < Real.sqrt ((q:ℝ)/(2*V)) := Real.sqrt_pos.mpr (by positivity)
    have hlampos : 0 < lam := lt_min hsqrtpos (by positivity)
    have hlamE : lam ≤ p / entryScale := min_le_right _ _
    -- two-sided Bernstein MGF.
    have hMGFpos : bernoulliExpectation p (fun Om => Real.exp (lam * Z Om))
        ≤ Real.exp (V * lam^2) := by
      have h := centered_sampling_coefficient_bernstein_mgf p hppos hp1 B entryScale lam hent hEpos hlampos.le hlamE
      have hLHS : bernoulliExpectation p (fun Om => Real.exp (lam * Z Om))
          = bernoulliExpectation p (fun Om => Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Om p B))) := by
        unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _; rw [hZ]
      rw [hLHS]
      refine h.trans (le_of_eq ?_)
      rw [hVdef]; ring
    have hMGFneg : bernoulliExpectation p (fun Om => Real.exp (-(lam * Z Om)))
        ≤ Real.exp (V * lam^2) := by
      -- -Z = Coeff of -B; apply Bernstein to -B.
      have h := centered_sampling_coefficient_bernstein_mgf p hppos hp1 (-B) entryScale lam
        (by rw [entrySup_neg]; exact hent) hEpos hlampos.le hlamE
      rw [frobSq_neg] at h
      -- h : E[exp(lam * matrixEntrySum(cSF Om p (-B)))] ≤ exp(lam^2 ((1-p)/p) frobNormSq B)
      have hrw : bernoulliExpectation p (fun Om => Real.exp (-(lam * Z Om)))
          = bernoulliExpectation p (fun Om => Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Om p (-B)))) := by
        unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _
        simp only [hZ, coeff_neg]; congr 1; ring
      rw [hrw]
      refine h.trans (le_of_eq ?_)
      rw [hVdef]; ring
    -- moment-from-MGF with M = exp(V lam^2), q := (q:ℝ).
    have hmom := bernoulli_moment_from_two_sided_mgf p hp0 hp1 Z lam (Real.exp (V * lam^2)) (q:ℝ)
      hlampos hqR hMGFpos hMGFneg
    -- hmom : E[|Z|^(q:ℝ)] ≤ 2 (q/(lam e))^q exp(V lam^2)
    -- bridge |Z|^(q:ℕ) = |Z|^((q:ℝ)).
    have hbridge : bernoulliExpectation p (fun Om => |Z Om| ^ q)
        = bernoulliExpectation p (fun Om => |Z Om| ^ (q:ℝ)) := by
      unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _
      simp only []; rw [Real.rpow_natCast]
    rw [hbridge]
    refine hmom.trans ?_
    -- 2 (q/(lam e))^q exp(V lam^2) = 2 (q/(e lam))^q exp(lam^2 V) ≤ bound_step ≤ RHS
    have hbs := bound_step (q:ℝ) p V entryScale frobScale (by exact_mod_cast hq1) hppos hp1 hVpos hEpos hfrobS hVfrob
    -- align the lam in hbs (it uses min(√(q/(2V)), p/E)) with our lam = same.
    calc 2 * ((q:ℝ) / (lam * Real.exp 1)) ^ (q:ℝ) * Real.exp (V * lam^2)
        = 2 * ((q:ℝ) / (Real.exp 1 * lam)) ^ (q:ℝ) * Real.exp (lam^2 * V) := by
          rw [mul_comm lam (Real.exp 1), mul_comm V (lam^2)]
      _ ≤ (2 * Real.sqrt 2 * (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale)) ^ (q:ℝ) := by
          rw [hlam]; exact hbs
      _ = (2 * Real.sqrt 2 * (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale)) ^ q := by
          rw [Real.rpow_natCast]
