-- Prove2me | solution 2 for mme_CW_q6_coupled_even_power_finite_extractions_below_raw
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T14:03:26.977705+00:00
-- url     : https://prove2.me/submissions/de7fb95c-d742-41cc-923e-247dd1903a2f

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_CW_q6_coupled_exact_floor_pruning
import Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below

open MME BigOperators Filter

lemma mmePad_one_le_mul.{u} {K : Type u} [Field K] {x y : TensorQ K 3}
    (hx : (tensorPreorder K).le 1 x) (hy : (tensorPreorder K).le 1 y) :
    (tensorPreorder K).le 1 (x * y) := by
  have h1 : (tensorPreorder K).le (1 * y) (x * y) :=
    (tensorPreorder K).mul_right 1 x hx y
  rw [one_mul] at h1
  exact (tensorPreorder K).le_trans _ _ _ hy h1

lemma mmePad_one_le_pow.{u} {K : Type u} [Field K] {x : TensorQ K 3} (hx : (tensorPreorder K).le 1 x) (n : ℕ) :
    (tensorPreorder K).le 1 (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (tensorPreorder K).le_refl 1
  | succ n ih => rw [pow_succ]; exact mmePad_one_le_mul ih hx

lemma mmePad_pow_le_pow_add.{u} {K : Type u} [Field K] {x : TensorQ K 3} (hx : (tensorPreorder K).le 1 x) (m s : ℕ) :
    (tensorPreorder K).le (x ^ m) (x ^ (m + s)) := by
  have h1 : (tensorPreorder K).le (1 * x ^ m) (x ^ s * x ^ m) :=
    (tensorPreorder K).mul_right 1 (x ^ s) (mmePad_one_le_pow hx s) (x ^ m)
  rw [one_mul, ← pow_add, add_comm] at h1
  exact h1

/-- Padding: if the unit tensor restricts from `T`, lower Kronecker powers of `T`
restrict from higher ones. -/
lemma mmePad_restrict_kronPow_le.{u} {K : Type u} [Field K] {T : TensorObj K 3}
    (hT : TensorObj.Restrict TensorObj.oneObj T) (m s : ℕ) :
    TensorObj.Restrict (T.kronPow m) (T.kronPow (m + s)) := by
  have hx : (tensorPreorder K).le 1 (TensorQ.toQ T) :=
    (tensorPreorder_le_toQ TensorObj.oneObj T).mpr hT
  have h := mmePad_pow_le_pow_add hx m s
  rw [← TensorQ.toQ_kronPow, ← TensorQ.toQ_kronPow] at h
  exact (tensorPreorder_le_toQ _ _).mp h

/-- A matrix-multiplication extraction of positive weight from some power of `T`
forces `T` to be nonzero, hence `oneObj ≤ T`. -/
lemma mmePad_one_le_of_extraction.{u} {K : Type u} [Field K] {T : TensorObj K 3} {tau : ℝ} (htau : 0 < tau)
    {e k : ℕ} (he : 0 < e) {a b c : Fin k → ℕ}
    (hres : TensorObj.Restrict
      (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i))) (T.kronPow e))
    (hpos : 0 < ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) :
    TensorObj.Restrict TensorObj.oneObj T := by
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ,
      (0 : ℝ) < (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
    by_contra hcon
    push Not at hcon
    have : ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) ≤ 0 :=
      Finset.sum_nonpos (fun i hi => hcon i hi)
    linarith
  have hne : a i * b i * c i ≠ 0 := by
    intro h0
    rw [h0] at hi
    simp [Real.zero_rpow htau.ne'] at hi
  have ha : 1 ≤ a i := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
  have hb : 1 ≤ b i := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
  have hc : 1 ≤ c i := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
  have h1 : (tensorPreorder K).le 1 (MMq K (a i) (b i) (c i)) := by
    rw [← MMq_one]; exact MMq_le_of_le ha hb hc
  have h2 : (tensorPreorder K).le (MMq K (a i) (b i) (c i))
      (TensorQ.toQ (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))) := by
    rw [TensorQ.toQ_bigAdd]
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => TensorQ.toQ (MMObj K (a j) (b j) (c j))) (Finset.mem_univ i)]
    have h0 := (tensorPreorder K).zero_le
      (∑ j ∈ Finset.univ.erase i, TensorQ.toQ (MMObj K (a j) (b j) (c j)))
    have h3 := (tensorPreorder K).add_right 0 _ h0 (TensorQ.toQ (MMObj K (a i) (b i) (c i)))
    rw [zero_add, add_comm] at h3
    exact h3
  have h3 : (tensorPreorder K).le
      (TensorQ.toQ (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i))))
      (TensorQ.toQ (T.kronPow e)) :=
    (tensorPreorder_le_toQ _ _).mpr hres
  have h4 : (tensorPreorder K).le 1 (TensorQ.toQ T ^ e) := by
    rw [← TensorQ.toQ_kronPow]
    exact (tensorPreorder K).le_trans _ _ _ h1 ((tensorPreorder K).le_trans _ _ _ h2 h3)
  rcases (tensorPreorder K).lower_archimedean (TensorQ.toQ T) with h0 | h0
  · exfalso
    rw [h0, zero_pow he.ne'] at h4
    have h1' : (tensorPreorder K).le ((1 : ℕ) : TensorQ K 3) ((0 : ℕ) : TensorQ K 3) := by
      rw [Nat.cast_one, Nat.cast_zero]; exact h4
    have := ((tensorPreorder K).nat_order_embedding 1 0).mp h1'
    omega
  · exact (tensorPreorder_le_toQ TensorObj.oneObj T).mp h0

theorem solution.{u}
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      0 < L ∧ L + G = N ∧ 341 * L < 100 * G ∧
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  have hraw_pos : 0 < 4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2) := by
    positivity
  set raw : ℝ := 4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2) with hraw
  have htau_pos : 0 < tau := by linarith
  set V₁ : ℝ := (2 * V + raw) / 3 with hV₁
  set V₂ : ℝ := (V + 2 * raw) / 3 with hV₂
  have hV₁pos : 0 < V₁ := by linarith
  have hV₁V : V < V₁ := by linarith
  have hV₁V₂ : V₁ < V₂ := by linarith
  have hV₂raw : V₂ < raw := by linarith
  have hV₂pos : 0 < V₂ := by linarith
  have hT : HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V₂ :=
    mme_CW_q6_coupled_raw_cyclic_value_below tau htau V₂ hV₂pos.le hV₂raw
  obtain ⟨e, he, hext⟩ :=
    mme_HasTauValueAtLeast_multiple_extractions_below
      (cyclicSymmetrization (coupledObj K 6)) tau V₂ V₁ hV₂pos hV₁pos.le hV₁V₂ hT
  -- the source tensor dominates the unit tensor
  have hone : TensorObj.Restrict TensorObj.oneObj (cyclicSymmetrization (coupledObj K 6)) := by
    obtain ⟨k, a, b, c, hres, hsum⟩ := hext 1
    rw [one_mul] at hres hsum
    exact mmePad_one_le_of_extraction htau_pos he hres
      (lt_of_lt_of_le (pow_pos hV₁pos e) hsum)
  -- analytic slack: `V^(2N) ≤ V₁^(r e)` once `r e` is large, where `r = 2N / e`
  set θ : ℝ := V / V₁ with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hV hV₁pos.le
  have hθ1 : θ < 1 := (div_lt_one hV₁pos).mpr hV₁V
  set M : ℝ := max 1 V with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hVM : V ≤ M := le_max_right _ _
  have hMe : 0 < M ^ e := pow_pos (by linarith) e
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).eventually
      (gt_mem_nhds (inv_pos.mpr hMe)))
  have key : ∀ N : ℕ, n₀ + e ≤ N → V ^ (2 * N) ≤ V₁ ^ ((2 * N / e) * e) := by
    intro N hN
    have hdecomp : 2 * N = (2 * N / e) * e + 2 * N % e :=
      (Nat.div_add_mod' (2 * N) e).symm
    have hs_lt : 2 * N % e < e := Nat.mod_lt _ he
    have hre : n₀ ≤ (2 * N / e) * e := by
      generalize (2 * N / e) * e = m at hdecomp
      omega
    have hθre : θ ^ ((2 * N / e) * e) < (M ^ e)⁻¹ := hn₀ _ hre
    have hVθ : V = θ * V₁ := by rw [hθ, div_mul_cancel₀ _ hV₁pos.ne']
    calc V ^ (2 * N) = V ^ ((2 * N / e) * e) * V ^ (2 * N % e) := by
          rw [← pow_add, ← hdecomp]
      _ ≤ V ^ ((2 * N / e) * e) * M ^ e := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hV _)
          calc V ^ (2 * N % e) ≤ M ^ (2 * N % e) := pow_le_pow_left₀ hV hVM _
            _ ≤ M ^ e := pow_le_pow_right₀ hM1 hs_lt.le
      _ = θ ^ ((2 * N / e) * e) * M ^ e * V₁ ^ ((2 * N / e) * e) := by
          rw [hVθ, mul_pow]; ring
      _ ≤ 1 * V₁ ^ ((2 * N / e) * e) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hV₁pos.le _)
          calc θ ^ ((2 * N / e) * e) * M ^ e ≤ (M ^ e)⁻¹ * M ^ e :=
                mul_le_mul_of_nonneg_right hθre.le hMe.le
            _ = 1 := inv_mul_cancel₀ hMe.ne'
      _ = V₁ ^ ((2 * N / e) * e) := one_mul _
  have hfloor := mme_CW_q6_coupled_exact_floor_pruning tau htau
  have hext' : ∀ᶠ N : ℕ in atTop, ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
      V ^ (2 * N) ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
    rw [Filter.eventually_atTop]
    refine ⟨n₀ + e, fun N hN => ?_⟩
    obtain ⟨k, a, b, c, hres, hsum⟩ := hext (2 * N / e)
    refine ⟨k, a, b, c, ?_, (key N hN).trans hsum⟩
    refine TensorObj.Restrict.trans hres ?_
    have hle : 2 * N / e * e ≤ 2 * N := Nat.div_mul_le_self _ _
    have hpad := mmePad_restrict_kronPow_le hone (2 * N / e * e) (2 * N - 2 * N / e * e)
    rwa [Nat.add_sub_cancel' hle] at hpad
  filter_upwards [hfloor, hext'] with N hN1 hN2
  exact ⟨hN1.1, hN1.2.1, hN1.2.2, hN2⟩
