-- Prove2me | solution 1 for quadratic_neumann_section63_summary_scale_absorbed_cr_form_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T19:06:30.500727+00:00
-- url     : https://prove2.me/submissions/84a3f635-ff3e-48b6-aab3-6651274d5f88

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion

/-- Abstract scalar helper for the T3 bound: with `sqrtL ≤ L`, `μ₀²√N ≤ K²`,
`1 ≤ L`, `0 < C'`, `0 < K`, `0 < L`, and `0 ≤ sqrtL, 0 ≤ sqrtN`, we get
`sqrtL·μ₀²·(√N/(C'KL)²) ≤ 1/C'²`. -/
private lemma t3_scalar {sqrtL μ0sq sqrtN C' K L : ℝ}
    (hsqrtL0 : 0 ≤ sqrtL) (_hsqrtN0 : 0 ≤ sqrtN)
    (hsqrtLL : sqrtL ≤ L) (hμ0N : μ0sq * sqrtN ≤ K ^ 2)
    (hL1 : 1 ≤ L) (hCppos : 0 < C') (hKpos : 0 < K) (_hLpos : 0 < L) :
    sqrtL * μ0sq * (sqrtN / (C' * K * L) ^ 2) ≤ 1 / C' ^ 2 := by
  have hDpos : (0:ℝ) < C' * K * L := by positivity
  have hnum : sqrtL * (μ0sq * sqrtN) ≤ sqrtL * K ^ 2 :=
    mul_le_mul_of_nonneg_left hμ0N hsqrtL0
  have hrw : sqrtL * μ0sq * (sqrtN / (C' * K * L) ^ 2)
           = (sqrtL * (μ0sq * sqrtN)) / (C' * K * L) ^ 2 := by ring
  rw [hrw, div_le_div_iff₀ (pow_pos hDpos 2) (pow_pos hCppos 2)]
  have hDsq : (C' * K * L) ^ 2 = C' ^ 2 * K ^ 2 * L ^ 2 := by ring
  have hLL2 : L ≤ L ^ 2 := by nlinarith [hL1]
  calc (sqrtL * (μ0sq * sqrtN)) * C' ^ 2
      ≤ (sqrtL * K ^ 2) * C' ^ 2 := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ (L * K ^ 2) * C' ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hsqrtLL (by positivity)
    _ = L * (K ^ 2 * C' ^ 2) := by ring
    _ ≤ L ^ 2 * (K ^ 2 * C' ^ 2) := mul_le_mul_of_nonneg_right hLL2 (by positivity)
    _ = 1 * (C' * K * L) ^ 2 := by rw [hDsq]; ring

/-- Endgame constant absorption, stated abstractly in the four term-bounds. -/
private lemma endgame_absorb {Csec C' T1 T2 T3 T4 : ℝ}
    (hCsecpos : 0 < Csec) (hCp9 : 9 ≤ C')
    (hC16 : (16 * Csec) ^ ((2:ℝ)/3) ≤ C')
    (hT1 : T1 ≤ 1 / C' ^ 2) (hT2 : T2 ≤ 1 / C' ^ 2)
    (hT3 : T3 ≤ 1 / C' ^ 2) (hT4 : T4 ≤ 1 / C' ^ ((3:ℝ)/2)) :
    Csec * (T1 + T2 + T3 + T4) ≤ 1 / 8 := by
  have hCppos : 0 < C' := by linarith
  have hC32pos : (0:ℝ) < C' ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hCppos _
  have hC2pos : (0:ℝ) < C' ^ 2 := by positivity
  -- √C' ≥ 3  ⇒  3/C'^2 ≤ 1/C'^{3/2}
  have hsqrtC' : (3:ℝ) ≤ C' ^ ((1:ℝ)/2) := by
    have : (9:ℝ) ^ ((1:ℝ)/2) ≤ C' ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (by norm_num) hCp9 (by norm_num)
    have h9 : (9:ℝ) ^ ((1:ℝ)/2) = 3 := by
      rw [show (9:ℝ) = 3 ^ (2:ℕ) by norm_num, ← Real.rpow_natCast 3 2,
          ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h9] at this
  -- C'^2 = C'^{1/2} * C'^{3/2}
  have hsplit : C' ^ 2 = C' ^ ((1:ℝ)/2) * C' ^ ((3:ℝ)/2) := by
    rw [← Real.rpow_add hCppos, ← Real.rpow_natCast C' 2]
    norm_num
  -- 3/C'^2 ≤ 1/C'^{3/2}
  have h3le : (3:ℝ) / C' ^ 2 ≤ 1 / C' ^ ((3:ℝ)/2) := by
    rw [hsplit, div_le_div_iff₀ (by positivity) hC32pos, one_mul]
    exact mul_le_mul_of_nonneg_right hsqrtC' (le_of_lt hC32pos)
  -- sum bound: T1+T2+T3+T4 ≤ 3/C'^2 + 1/C'^{3/2} ≤ 2/C'^{3/2}
  have hsum : T1 + T2 + T3 + T4 ≤ 2 / C' ^ ((3:ℝ)/2) := by
    have h1 : T1 + T2 + T3 ≤ 3 / C' ^ 2 := by
      have : (1:ℝ)/C'^2 + 1/C'^2 + 1/C'^2 = 3/C'^2 := by ring
      linarith [hT1, hT2, hT3, this.le, this.ge]
    have h2 : (2:ℝ) / C' ^ ((3:ℝ)/2) = 1 / C' ^ ((3:ℝ)/2) + 1 / C' ^ ((3:ℝ)/2) := by
      ring
    linarith [h1, h3le, hT4, h2.le, h2.ge]
  -- C'^{3/2} ≥ 16 Csec
  have hC3216 : (16:ℝ) * Csec ≤ C' ^ ((3:ℝ)/2) := by
    have hbase0 : (0:ℝ) ≤ 16 * Csec := by positivity
    have hmono : ((16 * Csec) ^ ((2:ℝ)/3)) ^ ((3:ℝ)/2) ≤ C' ^ ((3:ℝ)/2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase0 _) hC16 (by norm_num)
    have hround : ((16 * Csec) ^ ((2:ℝ)/3)) ^ ((3:ℝ)/2) = 16 * Csec := by
      rw [← Real.rpow_mul hbase0]
      norm_num
    rwa [hround] at hmono
  -- 2/C'^{3/2} ≤ 1/(8 Csec)
  have hfin : (2:ℝ) / C' ^ ((3:ℝ)/2) ≤ 1 / (8 * Csec) := by
    rw [div_le_div_iff₀ hC32pos (by positivity)]
    -- 2 * (8 Csec) ≤ 1 * C'^{3/2}
    nlinarith [hC3216]
  -- combine
  have hCsum : Csec * (T1 + T2 + T3 + T4) ≤ Csec * (2 / C' ^ ((3:ℝ)/2)) :=
    mul_le_mul_of_nonneg_left hsum (le_of_lt hCsecpos)
  have hCfin : Csec * (2 / C' ^ ((3:ℝ)/2)) ≤ Csec * (1 / (8 * Csec)) :=
    mul_le_mul_of_nonneg_left hfin (le_of_lt hCsecpos)
  have hlast : Csec * (1 / (8 * Csec)) = 1 / 8 := by
    field_simp
  linarith [hCsum, hCfin, hlast.le, hlast.ge]

set_option maxHeartbeats 600000 in
theorem solution (Csec : ℝ) :
    0 < Csec →
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        2 ≤ max n₁ n₂ →
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (let N : ℝ := ↑(max n₁ n₂)
         let R : ℝ := (r : ℝ)
         let Mobs : ℝ := (m : ℝ)
         let logN : ℝ := Real.log N
         Csec *
           ((μ₀ ^ 2 * μ₁) *
              Real.sqrt ((N * R * (β * logN)) / Mobs) *
                ((N * R) / Mobs) ^ 2 +
            μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
            Real.sqrt (β * logN) *
                Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                  (μ₀ ^ 2 * Real.sqrt R) +
            μ₀ * μ₁ *
              Real.rpow
                ((N * R * (β * logN)) / Mobs)
                ((3 : ℝ) / 2))) ≤
          (1 : ℝ) / 8 := by
  intro hCsecpos
  refine ⟨max 9 (Real.rpow (16 * Csec) (2 / 3)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro C' hCC' β hβ n₁ n₂ r m M μ₀ μ₁ S hmax hn1 hn2 hr hfeas hμ0 hμ1 _ _ hsample
  -- Constant lower bounds
  have hC9 : (9 : ℝ) ≤ max 9 (Real.rpow (16 * Csec) (2 / 3)) := le_max_left _ _
  have hCp9 : (9 : ℝ) ≤ C' := le_trans hC9 hCC'
  have hCppos : (0 : ℝ) < C' := by linarith
  have hCp1 : (1 : ℝ) ≤ C' := by linarith
  -- Set up notation
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hNdef
  set R : ℝ := (r : ℝ) with hRdef
  set Mobs : ℝ := (m : ℝ) with hMdef
  set L : ℝ := β * Real.log N with hLdef
  set K : ℝ := max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                (μ₀ * Real.rpow N ((1 : ℝ) / 4)) with hKdef
  -- Basic facts on N
  have hN2 : (2 : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast hmax
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hlogpos : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hβpos : (0 : ℝ) < β := by linarith
  have hLpos : (0 : ℝ) < L := by rw [hLdef]; exact mul_pos hβpos hlogpos
  have hL0 : (0 : ℝ) ≤ L := le_of_lt hLpos
  -- 1 ≤ L
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogN2 : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) hN2
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have : (2 : ℝ) * Real.log 2 ≤ β * Real.log N := by
      apply mul_le_mul (le_of_lt hβ) hlogN2 (le_of_lt (by linarith)) (by linarith)
    nlinarith [this, hlog2]
  -- μ₀, μ₁ positivity
  have hμ00 : (0 : ℝ) ≤ μ₀ := by linarith
  have hμ10 : (0 : ℝ) ≤ μ₁ := by linarith
  have hRpos : (0 : ℝ) < R := by rw [hRdef]; exact_mod_cast hr
  have hR0 : (0 : ℝ) ≤ R := le_of_lt hRpos
  -- rpow N (1/4) ≥ 1
  have hrpowN14 : (1 : ℝ) ≤ Real.rpow N ((1 : ℝ) / 4) :=
    Real.one_le_rpow hN1 (by norm_num)
  -- K facts
  have hKμ0N14 : μ₀ * Real.rpow N ((1 : ℝ) / 4) ≤ K := by
    rw [hKdef]; exact le_max_right _ _
  have hKμ1sq : μ₁ ^ 2 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hKsqrtμ0μ1 : Real.sqrt μ₀ * μ₁ ≤ K := by
    rw [hKdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hμ0K : μ₀ ≤ K := by
    have : μ₀ ≤ μ₀ * Real.rpow N ((1 : ℝ) / 4) :=
      le_mul_of_one_le_right hμ00 hrpowN14
    linarith [hKμ0N14]
  have hK1 : (1 : ℝ) ≤ K := le_trans hμ0 hμ0K
  have hKpos : (0 : ℝ) < K := by linarith
  have hK0 : (0 : ℝ) ≤ K := le_of_lt hKpos
  -- Sample hypothesis in clean form: C' * K * N * R * L ≤ Mobs
  have hsample' : C' * K * N * R * L ≤ Mobs := by
    rw [hMdef]
    have := hsample
    rw [hKdef, hLdef]
    -- hsample : (m:ℝ) ≥ C' * (max ...) * N * R * (β * log N)
    calc C' * K * N * R * L = C' * (max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow N ((1 : ℝ) / 4))) * N * R * (β * Real.log N) := by
            rw [hKdef, hLdef]
      _ ≤ (m : ℝ) := by rw [hNdef]; exact hsample
  -- Positivity of Mobs
  have hMpos : (0 : ℝ) < Mobs := by
    have hrhs : (0 : ℝ) < C' * K * N * R * L := by positivity
    linarith [hsample']
  have hMobs0 : (0 : ℝ) ≤ Mobs := le_of_lt hMpos
  -- A := N*R/Mobs
  set A : ℝ := (N * R) / Mobs with hAdef
  have hApos : (0 : ℝ) < A := by rw [hAdef]; positivity
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hApos
  -- Workhorse: A * (C'*K*L) ≤ 1
  have hAL1 : A * (C' * K * L) ≤ 1 := by
    rw [hAdef, div_mul_eq_mul_div, div_le_one hMpos]
    nlinarith [hsample', hNpos, hRpos, hKpos, hLpos, hCppos]
  -- Workhorse: (A*L) * (C'*K) ≤ 1
  have hALK1 : (A * L) * (C' * K) ≤ 1 := by
    have : (A * L) * (C' * K) = A * (C' * K * L) := by ring
    rw [this]; exact hAL1
  -- Feasibility: C' * K * R * L ≤ N  (from m ≤ n₁ n₂ ≤ N²)
  have hn1N : (n₁ : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast le_max_left _ _
  have hn2N : (n₂ : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast le_max_right _ _
  have hMleN2 : Mobs ≤ N * N := by
    rw [hMdef]
    have hcast : ((m : ℝ)) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hfeas
    have hprod : ((n₁ * n₂ : ℕ) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by push_cast; ring
    rw [hprod] at hcast
    have : (n₁ : ℝ) * (n₂ : ℝ) ≤ N * N :=
      mul_le_mul hn1N hn2N (by positivity) hN0
    linarith
  have hFeasN : C' * K * R * L ≤ N := by
    -- C'*K*N*R*L ≤ Mobs ≤ N*N  ⇒ divide by N
    have h1 : C' * K * N * R * L ≤ N * N := le_trans hsample' hMleN2
    have h2 : (C' * K * R * L) * N ≤ N * N := by nlinarith [h1]
    exact le_of_mul_le_mul_right h2 hNpos
  -- Unfold the let-bindings in the goal
  show Csec *
      ((μ₀ ^ 2 * μ₁) * Real.sqrt ((N * R * (β * Real.log N)) / Mobs) *
          ((N * R) / Mobs) ^ 2 +
        μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
        Real.sqrt (β * Real.log N) * Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
            (μ₀ ^ 2 * Real.sqrt R) +
        μ₀ * μ₁ * Real.rpow ((N * R * (β * Real.log N)) / Mobs) ((3 : ℝ) / 2)) ≤
      (1 : ℝ) / 8
  -- Rewrite arguments in terms of A, L
  have hAeq : (N * R) / Mobs = A := hAdef.symm
  have hALeq : (N * R * (β * Real.log N)) / Mobs = A * L := by
    rw [hAdef, hLdef]; ring
  rw [hAeq, hALeq]
  -- Now goal: Csec * (T1 + T2 + T3 + T4) ≤ 1/8 with
  -- T1 = μ₀^2*μ₁ * √(A*L) * A^2
  -- T2 = μ₀^2 * A^2
  -- T3 = √L * (A)^{3/2} * (μ₀^2 * √R)
  -- T4 = μ₀*μ₁ * (A*L)^{3/2}
  ------------------------------------------------------------------
  -- Half-power facts (all in Real.rpow / Real.sqrt)
  ------------------------------------------------------------------
  -- P := C' * K ≥ 9
  have hPpos : (0 : ℝ) < C' * K := mul_pos hCppos hKpos
  have hP0 : (0 : ℝ) ≤ C' * K := le_of_lt hPpos
  -- A*L ≤ 1/(C'*K)
  have hAL_le : A * L ≤ 1 / (C' * K) := by
    rw [le_div_iff₀ hPpos]; exact hALK1
  -- A ≤ 1/(C'*K)  (since L ≥ 1)
  have hA_leP : A ≤ 1 / (C' * K) := by
    have : A * L ≤ 1 / (C' * K) := hAL_le
    have hAL : A ≤ A * L := le_mul_of_one_le_right hA0 hL1
    linarith
  -- A ≤ 1/(C'*K*L)
  have hA_le : A ≤ 1 / (C' * K * L) := by
    rw [le_div_iff₀ (by positivity)]; exact hAL1
  ------------------------------------------------------------------
  -- Coherence power facts vs K
  ------------------------------------------------------------------
  -- μ₀^2 ≤ K^2
  have hμ0sqK2 : μ₀ ^ 2 ≤ K ^ 2 := by
    apply pow_le_pow_left₀ hμ00 hμ0K
  -- μ₁ ≤ K^{1/2}  (from μ₁^2 ≤ K)
  have hμ1_le_sqrtK : μ₁ ≤ Real.sqrt K := by
    rw [show K = K from rfl]
    have : μ₁ = Real.sqrt (μ₁ ^ 2) := by
      rw [Real.sqrt_sq hμ10]
    rw [this]
    exact Real.sqrt_le_sqrt hKμ1sq
  ------------------------------------------------------------------
  -- A^2 ≤ (1/(C'K))^2  and useful div facts
  ------------------------------------------------------------------
  have hA2_le : A ^ 2 ≤ (1 / (C' * K)) ^ 2 :=
    pow_le_pow_left₀ hA0 hA_leP 2
  -- (1/(C'K))^2 = 1/(C'^2 * K^2)
  have hinvP2 : (1 / (C' * K)) ^ 2 = 1 / (C' ^ 2 * K ^ 2) := by
    rw [div_pow, one_pow, mul_pow]
  ------------------------------------------------------------------
  -- T2 ≤ 1/C'^2
  ------------------------------------------------------------------
  have hT2 : μ₀ ^ 2 * A ^ 2 ≤ 1 / C' ^ 2 := by
    have h1 : μ₀ ^ 2 * A ^ 2 ≤ K ^ 2 * (1 / (C' * K)) ^ 2 :=
      mul_le_mul hμ0sqK2 hA2_le (by positivity) (by positivity)
    have h2 : K ^ 2 * (1 / (C' * K)) ^ 2 = 1 / C' ^ 2 := by
      rw [hinvP2]; field_simp
    linarith [h1, h2.le, h2.ge]
  ------------------------------------------------------------------
  -- T1 ≤ 1/C'^2 :  μ₀^2 * μ₁ * √(A*L) * A^2
  ------------------------------------------------------------------
  -- μ₁ * √(A*L) ≤ 1
  have hμ1sqrtAL : μ₁ * Real.sqrt (A * L) ≤ 1 := by
    -- √(A*L) ≤ √(1/(C'K))
    have hs1 : Real.sqrt (A * L) ≤ Real.sqrt (1 / (C' * K)) :=
      Real.sqrt_le_sqrt hAL_le
    -- √(1/(C'K)) = 1/√(C'K)
    have hs2 : Real.sqrt (1 / (C' * K)) = 1 / Real.sqrt (C' * K) := by
      rw [Real.sqrt_div' 1 hP0, Real.sqrt_one]
    -- μ₁ ≤ √K ≤ √(C'K)
    have hsqrtK_le : Real.sqrt K ≤ Real.sqrt (C' * K) := by
      apply Real.sqrt_le_sqrt
      exact le_mul_of_one_le_left hK0 hCp1
    have hμ1CK : μ₁ ≤ Real.sqrt (C' * K) := le_trans hμ1_le_sqrtK hsqrtK_le
    have hsqrtCKpos : (0 : ℝ) < Real.sqrt (C' * K) := Real.sqrt_pos.mpr hPpos
    have hs3 : Real.sqrt (A * L) ≤ 1 / Real.sqrt (C' * K) := by rw [← hs2]; exact hs1
    have hmm : μ₁ * Real.sqrt (A * L)
             ≤ Real.sqrt (C' * K) * (1 / Real.sqrt (C' * K)) :=
      mul_le_mul hμ1CK hs3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hone : Real.sqrt (C' * K) * (1 / Real.sqrt (C' * K)) = 1 :=
      mul_one_div_cancel (ne_of_gt hsqrtCKpos)
    linarith [hmm, hone.le, hone.ge]
  have hT1 : (μ₀ ^ 2 * μ₁) * Real.sqrt (A * L) * A ^ 2 ≤ 1 / C' ^ 2 := by
    -- rearrange as μ₀^2 * (μ₁ * √(A*L)) * A^2
    have hrw : (μ₀ ^ 2 * μ₁) * Real.sqrt (A * L) * A ^ 2
             = μ₀ ^ 2 * (μ₁ * Real.sqrt (A * L)) * A ^ 2 := by ring
    rw [hrw]
    have h1 : μ₀ ^ 2 * (μ₁ * Real.sqrt (A * L)) * A ^ 2
            ≤ K ^ 2 * 1 * (1 / (C' * K)) ^ 2 := by
      apply mul_le_mul (mul_le_mul hμ0sqK2 hμ1sqrtAL (by positivity) (by positivity))
        hA2_le (by positivity) (by positivity)
    have h2 : K ^ 2 * 1 * (1 / (C' * K)) ^ 2 = 1 / C' ^ 2 := by
      rw [hinvP2]; field_simp
    linarith [h1, h2.le, h2.ge]
  ------------------------------------------------------------------
  -- T4 ≤ 1/C'^{3/2} :  μ₀ * μ₁ * (A*L)^{3/2}
  ------------------------------------------------------------------
  -- (A*L)^{3/2} ≤ (1/(C'K))^{3/2}
  have hAL_rpow : (A * L) ^ ((3 : ℝ) / 2) ≤ (1 / (C' * K)) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) hAL_le (by norm_num)
  -- (1/(C'K))^{3/2} = 1 / (C'^{3/2} * K^{3/2})
  have hCK_rpow_div : (1 / (C' * K)) ^ ((3 : ℝ) / 2)
      = 1 / (C' ^ ((3:ℝ)/2) * K ^ ((3:ℝ)/2)) := by
    rw [Real.div_rpow (by norm_num) hP0, Real.one_rpow,
        Real.mul_rpow (le_of_lt hCppos) hK0]
  -- μ₀ * μ₁ ≤ √μ₀ * K
  have hμ0μ1 : μ₀ * μ₁ ≤ Real.sqrt μ₀ * K := by
    have hsq : Real.sqrt μ₀ * Real.sqrt μ₀ = μ₀ := Real.mul_self_sqrt hμ00
    have h : Real.sqrt μ₀ * (Real.sqrt μ₀ * μ₁) ≤ Real.sqrt μ₀ * K :=
      mul_le_mul_of_nonneg_left hKsqrtμ0μ1 (Real.sqrt_nonneg _)
    calc μ₀ * μ₁ = Real.sqrt μ₀ * Real.sqrt μ₀ * μ₁ := by rw [hsq]
      _ = Real.sqrt μ₀ * (Real.sqrt μ₀ * μ₁) := by ring
      _ ≤ Real.sqrt μ₀ * K := h
  -- √μ₀ ≤ K^{1/2}
  have hsqrtμ0_le : Real.sqrt μ₀ ≤ K ^ ((1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hμ00 hμ0K (by norm_num)
  have hK32pos : (0:ℝ) < K ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hKpos _
  have hK12pos : (0:ℝ) < K ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hKpos _
  have hC32pos : (0:ℝ) < C' ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hCppos _
  -- K^{3/2} = K^{1/2} * K
  have hK32_split : K ^ ((3:ℝ)/2) = K ^ ((1:ℝ)/2) * K := by
    rw [show ((3:ℝ)/2) = (1:ℝ)/2 + 1 by norm_num, Real.rpow_add hKpos, Real.rpow_one]
  have hT4 : μ₀ * μ₁ * (A * L) ^ ((3 : ℝ) / 2) ≤ 1 / C' ^ ((3:ℝ)/2) := by
    have step1 : μ₀ * μ₁ * (A * L) ^ ((3 : ℝ) / 2)
               ≤ (Real.sqrt μ₀ * K) * (1 / (C' * K)) ^ ((3 : ℝ) / 2) :=
      mul_le_mul hμ0μ1 hAL_rpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    have step2 : (Real.sqrt μ₀ * K) * (1 / (C' * K)) ^ ((3 : ℝ) / 2)
               ≤ 1 / C' ^ ((3:ℝ)/2) := by
      rw [hCK_rpow_div, hK32_split, mul_one_div]
      rw [div_le_div_iff₀ (by positivity) hC32pos]
      have hle : Real.sqrt μ₀ * K ≤ K ^ ((1:ℝ)/2) * K :=
        mul_le_mul_of_nonneg_right hsqrtμ0_le hK0
      have hmul : (Real.sqrt μ₀ * K) * C' ^ ((3:ℝ)/2)
                ≤ (K ^ ((1:ℝ)/2) * K) * C' ^ ((3:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hle (le_of_lt hC32pos)
      calc (Real.sqrt μ₀ * K) * C' ^ ((3:ℝ)/2)
          ≤ (K ^ ((1:ℝ)/2) * K) * C' ^ ((3:ℝ)/2) := hmul
        _ = 1 * (C' ^ ((3:ℝ)/2) * (K ^ ((1:ℝ)/2) * K)) := by ring
    linarith [step1, step2]
  ------------------------------------------------------------------
  -- T3 ≤ 1/C'^2 :  √L * A^{3/2} * (μ₀^2 * √R)   (uses feasibility)
  ------------------------------------------------------------------
  -- feasibility: R ≤ N/(C'*K*L)
  have hR_le : R ≤ N / (C' * K * L) := by
    rw [le_div_iff₀ (by positivity)]
    -- R * (C'*K*L) ≤ N  from hFeasN : C'*K*R*L ≤ N
    have : R * (C' * K * L) = C' * K * R * L := by ring
    rw [this]; exact hFeasN
  -- μ₀^2 * √N ≤ K^2 :  (μ₀ * N^{1/4})^2 = μ₀^2 * √N ≤ K^2
  have hμ0N_le : μ₀ ^ 2 * Real.sqrt N ≤ K ^ 2 := by
    have hid : (μ₀ * N ^ ((1:ℝ)/4)) ^ 2 = μ₀ ^ 2 * Real.sqrt N := by
      rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (N ^ ((1:ℝ)/4)) 2,
          ← Real.rpow_mul hN0]
      norm_num
    have hsq : (μ₀ * N ^ ((1:ℝ)/4)) ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (by positivity) hKμ0N14 2
    rw [hid] at hsq; exact hsq
  -- A^{3/2} ≤ (1/(C'*K*L))^{3/2}
  have hA32_le : A ^ ((3:ℝ)/2) ≤ (1 / (C' * K * L)) ^ ((3:ℝ)/2) :=
    Real.rpow_le_rpow hA0 hA_le (by norm_num)
  -- √R ≤ √(N/(C'*K*L))
  have hsqrtR_le : Real.sqrt R ≤ Real.sqrt (N / (C' * K * L)) :=
    Real.sqrt_le_sqrt hR_le
  -- D := C'*K*L > 0
  have hDpos : (0:ℝ) < C' * K * L := by positivity
  have hD0 : (0:ℝ) ≤ C' * K * L := le_of_lt hDpos
  -- (1/D)^{3/2} * √(N/D) = √N / D^2
  have hprodid : (1 / (C' * K * L)) ^ ((3:ℝ)/2) * Real.sqrt (N / (C' * K * L))
               = Real.sqrt N / (C' * K * L) ^ 2 := by
    rw [Real.div_rpow (by norm_num) hD0, Real.one_rpow,
        Real.sqrt_div' N hD0]
    -- 1/D^{3/2} * (√N/√D) = √N / D^2
    have hDrpow : (C' * K * L) ^ ((3:ℝ)/2) * Real.sqrt (C' * K * L)
                = (C' * K * L) ^ 2 := by
      rw [Real.sqrt_eq_rpow,
          ← Real.rpow_add hDpos,
          show ((3:ℝ)/2 + 1/2) = ((2:ℕ):ℝ) by norm_num,
          Real.rpow_natCast]
    field_simp
    rw [hDrpow]; ring
  -- combine T3
  have hT3 : Real.sqrt L * A ^ ((3:ℝ)/2) * (μ₀ ^ 2 * Real.sqrt R) ≤ 1 / C' ^ 2 := by
    -- step: T3 ≤ √L * (1/D)^{3/2} * (μ₀^2 * √(N/D))
    have hb1 : Real.sqrt L * A ^ ((3:ℝ)/2) * (μ₀ ^ 2 * Real.sqrt R)
             ≤ Real.sqrt L * (1 / (C' * K * L)) ^ ((3:ℝ)/2)
                 * (μ₀ ^ 2 * Real.sqrt (N / (C' * K * L))) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left hA32_le (Real.sqrt_nonneg _)
      · exact mul_le_mul_of_nonneg_left hsqrtR_le (by positivity)
      · positivity
      · positivity
    -- rewrite the RHS using hprodid
    have hb2 : Real.sqrt L * (1 / (C' * K * L)) ^ ((3:ℝ)/2)
                 * (μ₀ ^ 2 * Real.sqrt (N / (C' * K * L)))
             = Real.sqrt L * μ₀ ^ 2 * (Real.sqrt N / (C' * K * L) ^ 2) := by
      rw [← hprodid]; ring
    -- now bound: √L * μ₀^2 * (√N / D^2) ≤ 1/C'^2  via abstract helper
    have hsqrtL_le_L : Real.sqrt L ≤ L := by
      rw [Real.sqrt_eq_rpow]
      calc L ^ ((1:ℝ)/2) ≤ L ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L := Real.rpow_one L
    have hb3 : Real.sqrt L * μ₀ ^ 2 * (Real.sqrt N / (C' * K * L) ^ 2)
             ≤ 1 / C' ^ 2 :=
      t3_scalar (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hsqrtL_le_L hμ0N_le
        hL1 hCppos hKpos hLpos
    linarith [hb1, hb2.le, hb2.ge, hb3]
  -- endgame: (16 Csec)^{2/3} ≤ C'
  have hC16 : (16 * Csec) ^ ((2:ℝ)/3) ≤ C' :=
    le_trans (le_max_right _ _) hCC'
  exact endgame_absorb hCsecpos hCp9 hC16 hT1 hT2 hT3 hT4
