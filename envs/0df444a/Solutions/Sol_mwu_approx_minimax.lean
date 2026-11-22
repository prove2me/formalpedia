-- Prove2me | solution 1 for mwu_approx_minimax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:12.336317+00:00
-- url     : https://prove2.me/submissions/c5738620-4297-4e9e-935a-ee4e0dde7bb9

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Theorems.Thm_boolGamePayoff_nonneg
public import Theorems.Thm_minimax_value_le_one
public import Theorems.Thm_mwu_potential_T_bound
section
@[expose] public section
open Finset
noncomputable section
private lemma weight_le_potential
    {C : Type*} [Fintype C] (cfg : MWUConfig C) (c : C) :
    cfg.weights c ≤ cfg.potential := by
  unfold MWUConfig.potential
  exact Finset.single_le_sum
    (fun c _ => le_of_lt (cfg.weights_pos c))
    (by simp)
private lemma mwu_weight_eq_pow_hitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ (T : ℕ) (c : C),
      (mwuConfig M η hη1 v hrow T).weights c =
        (1 - η) ^ (mwuHitCount M η hη1 v hrow T c)
  | 0, c => by
      simp [mwuConfig, mwuRun, mwuHitCount, mwuInit]
  | T + 1, c => by
      simp [mwuConfig, mwuRun, mwuHitCount, mwuUpdateWeights,
        mwu_weight_eq_pow_hitCount M η hη1 v hrow T c,
        mul_comm]
      split_ifs <;> ring
private lemma mwuHitCount_eq_sum_indicator
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ (T : ℕ) (c : C),
      (mwuHitCount M η hη1 v hrow T c : ℝ) =
        ∑ t : Fin T, if M (mwuRows M η hη1 v hrow T t) c then (1 : ℝ) else 0
  | 0, c => by
      simp [mwuHitCount, mwuRows, mwuRun]
  | T + 1, c => by
      simp only [mwuHitCount, mwuRows, mwuRun]
      push_cast
      rw [mwuHitCount_eq_sum_indicator M η hη1 v hrow T c]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
private lemma boolGamePayoff_empirical_eq_avg
    {R C : Type*} [Fintype R] [DecidableEq R]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → R) (M : R → C → Bool) (c : C) :
    boolGamePayoff M (empiricalPMF hT rs) c =
      (∑ t : Fin T, if M (rs t) c then (1 : ℝ) else 0) / T := by
  simp only [boolGamePayoff, empiricalPMF]
  conv_lhs => arg 2; ext r; rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  symm
  conv_lhs =>
    rw [show (∑ t : Fin T, if M (rs t) c then (1 : ℝ) else 0) =
      ∑ r : R, ∑ t ∈ univ.filter (fun t => rs t = r),
        (if M (rs t) c then (1 : ℝ) else 0) from by
      rw [← Finset.sum_biUnion (s := univ)]
      · congr 1; ext t; simp
      · intro r₁ _ r₂ _ hne
        simp only [Function.onFun, Finset.disjoint_filter]
        simp_all]
  congr 1
  ext r
  rw [Finset.sum_congr rfl (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht])]
  rw [Finset.sum_const, nsmul_eq_mul]
private lemma boolGamePayoff_empirical_eq_hitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    [DecidableEq R]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    {T : ℕ} (hT : 0 < T) (c : C) :
    boolGamePayoff M (empiricalPMF hT (mwuRows M η hη1 v hrow T)) c =
      (mwuHitCount M η hη1 v hrow T c : ℝ) / T := by
  rw [boolGamePayoff_empirical_eq_avg]
  rw [← mwuHitCount_eq_sum_indicator M η hη1 v hrow T c]
private lemma hitRate_from_potential
    {N H T : ℕ} {η v ε : ℝ}
    (hNpos : 0 < (N : ℝ))
    (hη : 0 < η) (hη1 : η < 1)
    (hv1 : v ≤ 1)
    (hTpos : 0 < T)
    (hpot :
      (1 - η) ^ H ≤ (N : ℝ) * (1 - η * v) ^ T)
    (hηsmall : η ≤ ε / 4)
    (hlargeT : Real.log (N : ℝ) / (η * T) ≤ ε / 4) :
    v - ε ≤ (H : ℝ) / T := by
  have hbase : 0 < 1 - η := by linarith
  have hbasev : 0 < 1 - η * v := by
    have hηv_le : η * v ≤ η := mul_le_of_le_one_right (le_of_lt hη) hv1
    linarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hHnonneg : 0 ≤ (H : ℝ) := by positivity
  have hlog :
      (H : ℝ) * Real.log (1 - η) ≤
        Real.log (N : ℝ) + (T : ℝ) * Real.log (1 - η * v) := by
    have h0 :
        Real.log ((1 - η) ^ H) ≤
          Real.log ((N : ℝ) * (1 - η * v) ^ T) := by
      exact Real.log_le_log (pow_pos hbase H) hpot
    rw [Real.log_pow,
      Real.log_mul hNne (pow_ne_zero T (ne_of_gt hbasev)),
      Real.log_pow] at h0
    simpa [mul_comm, mul_left_comm, mul_assoc] using h0
  have hlog_up : Real.log (1 - η * v) ≤ -η * v :=
    by linarith only [Real.log_le_sub_one_of_pos hbasev]
  have hlog_down : -η / (1 - η) ≤ Real.log (1 - η) := by
    have h := Real.one_sub_inv_le_log_of_pos hbase
    have hne : 1 - η ≠ 0 := by linarith
    have hrew : 1 - (1 - η)⁻¹ = -η / (1 - η) := by field_simp [hne]; ring
    simpa [hrew] using h
  have hTreal_nonneg : (0 : ℝ) ≤ T := by positivity
  have hanti :
      (T : ℝ) * η * v - Real.log (N : ℝ) ≤
        (H : ℝ) * (-Real.log (1 - η)) := by
    -- From hlog: H * log(1-η) ≤ log N + T * log(1-η*v)
    -- From hlog_up: log(1-η*v) ≤ -η*v, so T * log(1-η*v) ≤ T*(-η*v)
    -- Hence H * log(1-η) ≤ log N - T*η*v
    -- Since log(1-η) < 0 (as 0 < η < 1), -log(1-η) > 0
    -- So H * (-log(1-η)) ≥ -log N + T*η*v = T*η*v - log N
    have hscaled := mul_le_mul_of_nonneg_left hlog_up hTreal_nonneg
    linarith only [hlog, hscaled]
  have hcoef : -Real.log (1 - η) ≤ η / (1 - η) := by
    have : -η / (1 - η) = -(η / (1 - η)) := by ring
    linarith only [hlog_down, this]
  have hanti' :
      (T : ℝ) * η * v - Real.log (N : ℝ) ≤
        (H : ℝ) * (η / (1 - η)) :=
    le_trans hanti (mul_le_mul_of_nonneg_left hcoef hHnonneg)
  have hnum :
      (1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ)) ≤ (H : ℝ) * η := by
    have h1η_nonneg : 0 ≤ 1 - η := by linarith
    calc (1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ))
        ≤ (1 - η) * ((H : ℝ) * (η / (1 - η))) :=
          mul_le_mul_of_nonneg_left hanti' h1η_nonneg
      _ = (H : ℝ) * η := by field_simp [show (1 : ℝ) - η ≠ 0 by linarith]
  have hηTpos : 0 < η * (T : ℝ) := by positivity
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hTpos)
  have hrate0 :
      (1 - η) * v - ((1 - η) * Real.log (N : ℝ)) / (η * T) ≤ (H : ℝ) / T := by
    have hdiv :=
      div_le_div_of_nonneg_right hnum (show 0 ≤ η * (T : ℝ) by positivity)
    have hsimpL :
        ((1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ))) / (η * T) =
          (1 - η) * v - ((1 - η) * Real.log (N : ℝ)) / (η * T) := by
      field_simp [show η ≠ 0 from ne_of_gt hη, hTne]
    have hsimpR :
        ((H : ℝ) * η) / (η * T) = (H : ℝ) / T := by
      field_simp [show η ≠ 0 from ne_of_gt hη, hTne]
    simpa [hsimpL, hsimpR] using hdiv
  have hterm1 : v - ε / 4 ≤ (1 - η) * v := by
    linarith only [hηsmall, mul_le_of_le_one_right hη.le hv1]
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have haux : Real.log (N : ℝ) ≤ (ε / 4) * (η * T) := (div_le_iff₀ hηTpos).mp hlargeT
  have hterm2 :
      ((1 - η) * Real.log (N : ℝ)) / (η * T) ≤ ε / 4 := by
    apply (div_le_iff₀ hηTpos).2
    calc (1 - η) * Real.log (N : ℝ) ≤ 1 * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hη]) hlog_nonneg
      _ ≤ (ε / 4) * (η * T) := by simpa only [one_mul] using haux
  linarith only [hterm1, hterm2, hrate0, hη, hηsmall]
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty R] [Nonempty C]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
    v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C, v - ε ≤ boolGamePayoff M p c := by
  classical
  by_cases htriv : v ≤ ε
  · exact ⟨uniformPMF R, fun c =>
      le_trans (sub_nonpos.mpr htriv) (boolGamePayoff_nonneg M _ c)⟩
  have hεv : ε < v := lt_of_not_ge htriv
  have hv : 0 < v := lt_trans hε hεv
  have hv1 : v ≤ 1 := minimax_value_le_one M v hrow
  let η : ℝ := ε / 4
  have hη : 0 < η := by positivity
  have hη1 : η < 1 := by dsimp [η]; linarith
  let N : ℕ := Fintype.card C
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast @Fintype.card_pos C _ _
  let T : ℕ := max 1 (Nat.ceil (16 * Real.log (N : ℝ) / ε ^ 2))
  have hTpos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hTlarge0 : 16 * Real.log (N : ℝ) / ε ^ 2 ≤ (T : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast Nat.le_max_right 1 _
  have hlargeT : Real.log (N : ℝ) / (η * T) ≤ ε / 4 := by
    have hηTpos : 0 < η * (T : ℝ) := by positivity
    apply (div_le_iff₀ hηTpos).2
    have hε2pos : 0 < ε ^ 2 := by positivity
    have htmp : 16 * Real.log (N : ℝ) ≤ (T : ℝ) * ε ^ 2 := (div_le_iff₀ hε2pos).mp hTlarge0
    dsimp [η]; nlinarith
  let rows := mwuRows M η hη1 v hrow T
  let p := empiricalPMF hTpos rows
  refine ⟨p, fun c => ?_⟩
  have hpot :
      (1 - η) ^ (mwuHitCount M η hη1 v hrow T c) ≤
        (N : ℝ) * (1 - η * v) ^ T := by
    calc (1 - η) ^ (mwuHitCount M η hη1 v hrow T c)
        = (mwuConfig M η hη1 v hrow T).weights c :=
            (mwu_weight_eq_pow_hitCount M η hη1 v hrow T c).symm
      _ ≤ (mwuConfig M η hη1 v hrow T).potential := weight_le_potential _ c
      _ ≤ (N : ℝ) * (1 - η * v) ^ T := mwu_potential_T_bound M η (le_of_lt hη) hη1 v hrow T
  rw [boolGamePayoff_empirical_eq_hitCount M η hη1 v hrow hTpos c]
  exact hitRate_from_potential hNpos hη hη1 hv1 hTpos hpot (by dsimp [η]; linarith) hlargeT
