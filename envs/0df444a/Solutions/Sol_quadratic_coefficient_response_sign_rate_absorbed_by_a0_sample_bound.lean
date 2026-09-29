-- Prove2me | solution 1 for quadratic_coefficient_response_sign_rate_absorbed_by_a0_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T19:56:10.195803+00:00
-- url     : https://prove2.me/submissions/3c0a1bb3-3b50-4d32-8246-b24a1545a4e5

import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_min_dim
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Provec87

theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-- `1 ≤ β log n` for `β > 2`, `n ≥ 2`. -/
theorem one_le_beta_log (β n : ℝ) (hβ : 2 < β) (hn : 2 ≤ n) (hlogpos : 0 < Real.log n) :
    (1:ℝ) ≤ β * Real.log n := by
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have h4 : (1:ℝ) < Real.log 4 := by
    have : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_three (by norm_num)
    calc (1:ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [hlog2n, hlogpos, h4, hlog4]

/-- The core scalar estimate, plain-variable form to avoid the `set`-whnf storm.
* `K = Cscale*Csign ≥ 0`, `mu0,rr ≥ 1`, `nn = max ≥ 1`, `mm = min ≥ 1`, `mm ≤ nn`,
* `LL = β log n ≥ 1`, `lam ≥ 1`, feasibility
  `lam*mu0^(4/3)*nn*rr^(4/3)*LL ≤ mr ≤ nn*mm`.
Conclusion: the response scale
`K*mu0^2*rr^2/(nn*mm)*√(LL*nn*(nn*mm)/mr) ≤ K/lam`. -/
theorem core_bound
    (K mu0 rr nn mm mr LL lam : ℝ)
    (hK : 0 ≤ K) (hmu0 : 1 ≤ mu0) (hrr : 1 ≤ rr)
    (hnn : 1 ≤ nn) (hmm : 1 ≤ mm) (hmnle : mm ≤ nn)
    (hLL : 1 ≤ LL) (hlam : 1 ≤ lam)
    (hfeas_lb : lam * Real.rpow mu0 ((4:ℝ)/3) * nn * Real.rpow rr ((4:ℝ)/3) * LL ≤ mr)
    (hfeas_ub : mr ≤ nn * mm) :
    K * mu0 ^ 2 * rr ^ 2 / (nn * mm) *
        Real.sqrt (LL * nn * (nn * mm) / mr) ≤ K / lam := by
  have hmu0p : (0:ℝ) < mu0 := by linarith
  have hrrp : (0:ℝ) < rr := by linarith
  have hnnp : (0:ℝ) < nn := by linarith
  have hmmp : (0:ℝ) < mm := by linarith
  have hLLp : (0:ℝ) < LL := by linarith
  have hlamp : (0:ℝ) < lam := by linarith
  set D : ℝ := Real.rpow mu0 ((4:ℝ)/3) with hD
  set Dr : ℝ := Real.rpow rr ((4:ℝ)/3) with hDr
  have hDp : (0:ℝ) < D := by rw [hD, rpow_eq]; exact Real.rpow_pos_of_pos hmu0p _
  have hDrp : (0:ℝ) < Dr := by rw [hDr, rpow_eq]; exact Real.rpow_pos_of_pos hrrp _
  have hD1 : (1:ℝ) ≤ D := by
    rw [hD, rpow_eq]
    calc (1:ℝ) = (1:ℝ) ^ ((4:ℝ)/3) := (Real.one_rpow _).symm
      _ ≤ mu0 ^ ((4:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hmu0 (by norm_num)
  have hDr1 : (1:ℝ) ≤ Dr := by
    rw [hDr, rpow_eq]
    calc (1:ℝ) = (1:ℝ) ^ ((4:ℝ)/3) := (Real.one_rpow _).symm
      _ ≤ rr ^ ((4:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hrr (by norm_num)
  have hlbp : (0:ℝ) < lam * D * nn * Dr * LL := by positivity
  have hmrp : (0:ℝ) < mr := lt_of_lt_of_le hlbp hfeas_lb
  -- sqrt D = mu0^(2/3),  sqrt Dr = rr^(2/3)
  set E : ℝ := Real.rpow mu0 ((2:ℝ)/3) with hE
  set F : ℝ := Real.rpow rr ((2:ℝ)/3) with hF
  have hEp : (0:ℝ) < E := by rw [hE, rpow_eq]; exact Real.rpow_pos_of_pos hmu0p _
  have hFp : (0:ℝ) < F := by rw [hF, rpow_eq]; exact Real.rpow_pos_of_pos hrrp _
  have hsqrtD : Real.sqrt D = E := by
    rw [hD, hE, Real.sqrt_eq_rpow]; show (mu0 ^ ((4:ℝ)/3)) ^ ((1:ℝ)/2) = mu0 ^ ((2:ℝ)/3)
    rw [← Real.rpow_mul (le_of_lt hmu0p)]; norm_num
  have hsqrtDr : Real.sqrt Dr = F := by
    rw [hDr, hF, Real.sqrt_eq_rpow]; show (rr ^ ((4:ℝ)/3)) ^ ((1:ℝ)/2) = rr ^ ((2:ℝ)/3)
    rw [← Real.rpow_mul (le_of_lt hrrp)]; norm_num
  -- mu0^2 = D*E,  rr^2 = Dr*F
  have hmu0sq : mu0 ^ 2 = D * E := by
    rw [hD, hE, rpow_eq, rpow_eq, ← Real.rpow_natCast mu0 2, ← Real.rpow_add hmu0p]; norm_num
  have hrrsq : rr ^ 2 = Dr * F := by
    rw [hDr, hF, rpow_eq, rpow_eq, ← Real.rpow_natCast rr 2, ← Real.rpow_add hrrp]; norm_num
  -- Step A:  argument of sqrt ≤ nn * mm / (lam*D*Dr)
  -- because  LL*nn*(nn*mm)/mr ≤ LL*nn*(nn*mm)/(lam*D*nn*Dr*LL) = nn*mm/(lam*D*Dr).
  have hstepA : LL * nn * (nn * mm) / mr ≤ nn * mm / (lam * D * Dr) := by
    rw [div_le_div_iff₀ hmrp (by positivity)]
    -- (LL*nn*(nn*mm)) * (lam*D*Dr) ≤ (nn*mm) * mr
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt hnnp) (le_of_lt hmmp))
        (sub_nonneg.mpr hfeas_lb),
      mul_pos (mul_pos hlamp hDp) hDrp, hnnp, hmmp, hLLp]
  have hStepB : Real.sqrt (LL * nn * (nn * mm) / mr)
      ≤ Real.sqrt (nn * mm / (lam * D * Dr)) := Real.sqrt_le_sqrt hstepA
  -- sqrt(nn*mm/(lam*D*Dr)) = sqrt(nn)*sqrt(mm)/(sqrt lam * E * F)
  have hsqrtRHS : Real.sqrt (nn * mm / (lam * D * Dr))
      = Real.sqrt nn * Real.sqrt mm / (Real.sqrt lam * E * F) := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (le_of_lt hnnp),
      Real.sqrt_mul (by positivity), Real.sqrt_mul (le_of_lt hlamp), hsqrtD, hsqrtDr]
  have hsqrtlamp : (0:ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlamp
  have hsqrtmmp : (0:ℝ) < Real.sqrt mm := Real.sqrt_pos.mpr hmmp
  have hsqrtnnp : (0:ℝ) < Real.sqrt nn := Real.sqrt_pos.mpr hnnp
  have hKpre : (0:ℝ) ≤ K * mu0 ^ 2 * rr ^ 2 / (nn * mm) := by positivity
  -- product equality:  K*mu0^2*rr^2/(nn*mm) * (sqrt nn*sqrt mm/(sqrt lam*E*F))
  --   = K * D*Dr / (sqrt nn * sqrt mm * sqrt lam)   [E,F cancel; nn=√nn², mm=√mm²]
  have hsn : Real.sqrt nn * Real.sqrt nn = nn := Real.mul_self_sqrt (le_of_lt hnnp)
  have hsm : Real.sqrt mm * Real.sqrt mm = mm := Real.mul_self_sqrt (le_of_lt hmmp)
  have hprod_eq :
      K * mu0 ^ 2 * rr ^ 2 / (nn * mm) *
          (Real.sqrt nn * Real.sqrt mm / (Real.sqrt lam * E * F))
        = K * (D * Dr) / (Real.sqrt nn * Real.sqrt mm * Real.sqrt lam) := by
    rw [hmu0sq, hrrsq]
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    -- (K*(D*E)*(Dr*F)) * (√nn*√mm*√lam) = K*(D*Dr) * ((nn*mm)*(√lam*E*F))
    have : nn * mm = (Real.sqrt nn * Real.sqrt nn) * (Real.sqrt mm * Real.sqrt mm) := by
      rw [hsn, hsm]
    rw [this]; ring
  -- final scalar:  K*(D*Dr)/(sqrt nn*sqrt mm*sqrt lam) ≤ K/lam
  have hfinal_scalar :
      K * (D * Dr) / (Real.sqrt nn * Real.sqrt mm * Real.sqrt lam) ≤ K / lam := by
    -- feasibility tight:  lam * (D*Dr) ≤ mm
    have hchain : lam * D * nn * Dr * LL ≤ nn * mm := le_trans hfeas_lb hfeas_ub
    have hlamDDr_le_mm : lam * (D * Dr) ≤ mm := by
      have hge : lam * (D * Dr) * nn ≤ lam * D * nn * Dr * LL := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hlamp) (le_of_lt hDp))
          (le_of_lt hnnp)) (mul_nonneg (le_of_lt hDrp) (by linarith : (0:ℝ) ≤ LL - 1)),
          mul_pos (mul_pos (mul_pos hlamp hDp) hnnp) hDrp]
      have h2 : lam * (D * Dr) * nn ≤ mm * nn := by nlinarith [hge, hchain]
      exact le_of_mul_le_mul_right h2 hnnp
    -- key squared bound:  (D*Dr)^2 * lam ≤ nn*mm
    have hDDr1 : (1:ℝ) ≤ D * Dr := by nlinarith [hD1, hDr1, hDp, hDrp]
    have hsq : (D * Dr) ^ 2 * lam ≤ nn * mm := by
      -- (D*Dr)^2*lam = (D*Dr)*(lam*(D*Dr)) ≤ (D*Dr)*mm ≤ ... need ≤ nn*mm
      -- (D*Dr)*mm ≤ nn*mm  since D*Dr ≤ mm/lam ≤ mm ≤ nn
      have hDDr_le_mm : D * Dr ≤ mm := by nlinarith [hlamDDr_le_mm, hlam, hDp, hDrp]
      have hDDr_le_nn : D * Dr ≤ nn := le_trans hDDr_le_mm hmnle
      nlinarith [hlamDDr_le_mm, hDDr_le_nn, hDp, hDrp, hmmp, mul_pos hDp hDrp]
    -- ⇒  (D*Dr)*sqrt lam ≤ sqrt(nn*mm) = sqrt nn * sqrt mm
    have hsqrt_target : (D * Dr) * Real.sqrt lam ≤ Real.sqrt nn * Real.sqrt mm := by
      have hlhs_nn : (0:ℝ) ≤ (D * Dr) * Real.sqrt lam := by positivity
      have hrhs_nn : (0:ℝ) ≤ Real.sqrt nn * Real.sqrt mm := by positivity
      have hsqsq : ((D * Dr) * Real.sqrt lam) ^ 2 ≤ (Real.sqrt nn * Real.sqrt mm) ^ 2 := by
        have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt (le_of_lt hlamp)
        have hsn2 : Real.sqrt nn ^ 2 = nn := Real.sq_sqrt (le_of_lt hnnp)
        have hsm2 : Real.sqrt mm ^ 2 = mm := Real.sq_sqrt (le_of_lt hmmp)
        have hexpand1 : ((D * Dr) * Real.sqrt lam) ^ 2 = (D * Dr) ^ 2 * lam := by
          rw [mul_pow, hsl]
        have hexpand2 : (Real.sqrt nn * Real.sqrt mm) ^ 2 = nn * mm := by
          rw [mul_pow, hsn2, hsm2]
        rw [hexpand1, hexpand2]; exact hsq
      nlinarith [hsqsq, hlhs_nn, hrhs_nn]
    -- conclude:  K*(D*Dr)/(sqrt nn*sqrt mm*sqrt lam) ≤ K/lam
    rw [div_le_div_iff₀ (by positivity) hlamp]
    -- K*(D*Dr)*lam ≤ K*(sqrt nn*sqrt mm*sqrt lam)
    have hstep : (D * Dr) * lam ≤ Real.sqrt nn * Real.sqrt mm * Real.sqrt lam := by
      -- (D*Dr)*lam = ((D*Dr)*sqrt lam)*sqrt lam ≤ (sqrt nn*sqrt mm)*sqrt lam
      have hlamval : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt (le_of_lt hlamp)
      calc (D * Dr) * lam
          = ((D * Dr) * Real.sqrt lam) * Real.sqrt lam := by
            linear_combination (-(D * Dr)) * hlamval
        _ ≤ (Real.sqrt nn * Real.sqrt mm) * Real.sqrt lam :=
              mul_le_mul_of_nonneg_right hsqrt_target (le_of_lt hsqrtlamp)
        _ = Real.sqrt nn * Real.sqrt mm * Real.sqrt lam := by ring
    nlinarith [mul_le_mul_of_nonneg_left hstep hK, hK]
  calc K * mu0 ^ 2 * rr ^ 2 / (nn * mm) * Real.sqrt (LL * nn * (nn * mm) / mr)
      ≤ K * mu0 ^ 2 * rr ^ 2 / (nn * mm) *
          (Real.sqrt nn * Real.sqrt mm / (Real.sqrt lam * E * F)) := by
        apply mul_le_mul_of_nonneg_left _ hKpre
        rw [← hsqrtRHS]; exact hStepB
    _ = K * (D * Dr) / (Real.sqrt nn * Real.sqrt mm * Real.sqrt lam) := hprod_eq
    _ ≤ K / lam := hfinal_scalar

end Provec87

open Provec87 in
/-- `quadratic_coefficient_response_sign_rate_absorbed_by_a0_sample_bound`.
Reduction: bound the sign-matrix sup-norm via the A0 estimate
(`entry_sup_norm_sign_matrix_bound_from_a0_min_dim`), then absorb the resulting
scalar response rate into the `λ^{-1}` threshold using the Lemma 4.6 sample lower
bound (`core_bound`). -/
theorem solution
    (Cscale : ℝ) :
    0 < Cscale →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ → A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        entrySupNorm Y ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm (signMatrix S) →
        entrySupNorm Y ≤ Cthreshold * Real.rpow lam (-1) := by
  intro hCscale
  obtain ⟨Csign, hCsign, hsignbound⟩ := entry_sup_norm_sign_matrix_bound_from_a0_min_dim
  refine ⟨Cscale * Csign, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample Y hY
  -- abbreviations
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hμ₀0 : (0:ℝ) < μ₀ := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hr1R : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrR : (0:ℝ) < (r:ℝ) := by linarith
  -- E = entrySupNorm (signMatrix S) ≥ 0 and ≤ Csign μ₀ (r/min)
  set E : ℝ := entrySupNorm (signMatrix S) with hEdef
  have hEbound : E ≤ Csign * μ₀ * ((r:ℝ) / (↑(min n₁ n₂))) :=
    hsignbound n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hmaxpos : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (le_max_left _ _)
  have hminpos : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hmaxR : (0:ℝ) < (↑(max n₁ n₂):ℝ) := by exact_mod_cast hmaxpos
  have hminR : (0:ℝ) < (↑(min n₁ n₂):ℝ) := by exact_mod_cast hminpos
  have hCsignμ₀rmin_nn : (0:ℝ) ≤ Csign * μ₀ * ((r:ℝ) / (↑(min n₁ n₂))) := by positivity
  -- prefactor P ≥ 0
  set P : ℝ := Cscale * μ₀ * ((r:ℝ) / (↑(max n₁ n₂))) *
      Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
        ((m:ℝ) / ((n₁:ℝ) * (n₂:ℝ)))) with hPdef
  have hPnn : (0:ℝ) ≤ P := by rw [hPdef]; positivity
  -- E nonneg via being a ciSup of nonneg? Use: hEbound gives E ≤ (nonneg); not enough.
  -- Prove E ≥ 0 from definition: entrySupNorm = ⨆⨆ |·| ≥ 0.
  have hE0 : (0:ℝ) ≤ E := by
    rw [hEdef, entrySupNorm]
    apply Real.iSup_nonneg
    intro i
    apply Real.iSup_nonneg
    intro j
    exact abs_nonneg _
  -- Step 1:  entrySupNorm Y ≤ P * E ≤ P * (Csign μ₀ (r/min))
  have hY' : entrySupNorm Y ≤ P * (Csign * μ₀ * ((r:ℝ) / (↑(min n₁ n₂)))) := by
    calc entrySupNorm Y ≤ P * E := by rw [hPdef]; exact hY
      _ ≤ P * (Csign * μ₀ * ((r:ℝ) / (↑(min n₁ n₂)))) :=
            mul_le_mul_of_nonneg_left hEbound hPnn
  -- Step 2:  rewrite P*(Csign μ₀ (r/min)) into core_bound LHS shape, with
  --   K = Cscale*Csign, nn = max, mm = min, rr = r, LL = β log(max), mr = m.
  set nn : ℝ := (↑(max n₁ n₂):ℝ) with hnn_def
  set mm : ℝ := (↑(min n₁ n₂):ℝ) with hmm_def
  set rr : ℝ := (r:ℝ) with hrr_def
  set LL : ℝ := β * Real.log nn with hLL_def
  set mr : ℝ := (m:ℝ) with hmr_def
  -- nn*mm = n₁*n₂
  have hnnmm : nn * mm = (n₁:ℝ) * (n₂:ℝ) := by
    rw [hnn_def, hmm_def]
    rw [show ((↑(max n₁ n₂):ℝ)) * (↑(min n₁ n₂):ℝ) = ((max n₁ n₂ * min n₁ n₂ : ℕ):ℝ) by push_cast; ring]
    rw [max_mul_min]; push_cast; ring
  -- the prefactor product equals core LHS
  have hPexpand :
      P * (Csign * μ₀ * (rr / mm))
        = (Cscale * Csign) * μ₀ ^ 2 * rr ^ 2 / (nn * mm) *
            Real.sqrt (LL * nn * (nn * mm) / mr) := by
    rw [hPdef, hLL_def]
    rw [hnnmm]
    -- both sqrt arguments: (β*nn*log nn)/(m/(n₁n₂)) = (β*log nn)*nn*(n₁n₂)/m
    have hsqrtarg :
        (β * nn * Real.log nn) / (mr / ((n₁:ℝ) * (n₂:ℝ)))
          = (β * Real.log nn) * nn * ((n₁:ℝ) * (n₂:ℝ)) / mr := by
      rw [hmr_def]; field_simp
    rw [show ((β * (↑(max n₁ n₂):ℝ) * Real.log (↑(max n₁ n₂))) /
            ((m:ℝ) / ((n₁:ℝ) * (n₂:ℝ))))
          = (β * nn * Real.log nn) / (mr / ((n₁:ℝ) * (n₂:ℝ))) by
          rw [hnn_def, hmr_def]]
    rw [hsqrtarg]
    -- now algebra on the non-sqrt prefactors
    rw [hrr_def, ← hnnmm]
    field_simp
  -- Step 3:  apply core_bound
  have hmm_le_nn : mm ≤ nn := by
    rw [hnn_def, hmm_def]; exact_mod_cast min_le_max
  have hnn1 : (1:ℝ) ≤ nn := by rw [hnn_def]; exact_mod_cast hmaxpos
  have hmm1 : (1:ℝ) ≤ mm := by rw [hmm_def]; exact_mod_cast hminpos
  have hrr1 : (1:ℝ) ≤ rr := by rw [hrr_def]; exact hr1R
  -- LL ≥ 1 :  need max ≥ 2.  If max = 1 then n₁=n₂=1, log=0, but then sample bound forces m≥0 and
  -- the sqrt arg has log nn = 0 so P = 0; handle that edge separately.
  rcases lt_or_ge nn 2 with hnnlt2 | hnn2
  · -- edge case nn < 2 ⇒ nn = 1 (handled below); jump to it
    have hmaxnat1 : max n₁ n₂ = 1 := by
      have : (↑(max n₁ n₂):ℝ) < 2 := by rw [← hnn_def]; exact hnnlt2
      have hlt : max n₁ n₂ < 2 := by exact_mod_cast this
      omega
    have hnneq : nn = 1 := by rw [hnn_def, hmaxnat1]; norm_num
    have hlog0 : Real.log nn = 0 := by rw [hnneq]; simp
    have hP0 : P = 0 := by
      rw [hPdef]
      rw [show ((β * (↑(max n₁ n₂):ℝ) * Real.log (↑(max n₁ n₂))))
            = (β * nn * Real.log nn) by rw [hnn_def]]
      rw [hlog0]; simp
    have hYle0 : entrySupNorm Y ≤ 0 := by
      calc entrySupNorm Y ≤ P * E := by rw [hPdef]; exact hY
        _ = 0 := by rw [hP0]; ring
    have hRHSnn : (0:ℝ) ≤ (Cscale * Csign) * Real.rpow lam (-1) := by
      have : (0:ℝ) < Real.rpow lam (-1) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hlam0 _
      positivity
    exact le_trans hYle0 hRHSnn
  · -- main case nn ≥ 2
    have hlognpos : (0:ℝ) < Real.log nn := Real.log_pos (by linarith)
    have hLL1 : (1:ℝ) ≤ LL := by rw [hLL_def]; exact one_le_beta_log β nn hβ hnn2 hlognpos
    -- feasibility lower bound:  lam*μ₀^(4/3)*nn*r^(4/3)*LL ≤ mr
    have hfeas_lb : lam * Real.rpow μ₀ ((4:ℝ)/3) * nn * Real.rpow rr ((4:ℝ)/3) * LL ≤ mr := by
      rw [hmr_def, hnn_def, hrr_def, hLL_def, hnn_def]
      exact hsample
    have hfeas_ub : mr ≤ nn * mm := by rw [hnnmm, hmr_def]; exact_mod_cast hm
    have hcore := core_bound (Cscale * Csign) μ₀ rr nn mm mr LL lam
      (by positivity) hμ₀ hrr1 hnn1 hmm1 hmm_le_nn hLL1 hlam hfeas_lb hfeas_ub
    -- assemble:  entrySupNorm Y ≤ P*(...) = core LHS ≤ (Cscale*Csign)/lam = (Cscale*Csign)*lam^{-1}
    have hlaminv : Real.rpow lam (-1) = 1 / lam := by
      rw [rpow_eq, Real.rpow_neg_one, inv_eq_one_div]
    calc entrySupNorm Y ≤ P * (Csign * μ₀ * (rr / mm)) := by rw [hrr_def, hmm_def]; exact hY'
      _ = (Cscale * Csign) * μ₀ ^ 2 * rr ^ 2 / (nn * mm) *
            Real.sqrt (LL * nn * (nn * mm) / mr) := hPexpand
      _ ≤ (Cscale * Csign) / lam := hcore
      _ = (Cscale * Csign) * Real.rpow lam (-1) := by rw [hlaminv]; ring
