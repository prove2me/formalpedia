-- Prove2me | solution 1 for syracuse_valuation_deficit_small_times_zero_log_density
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:11:10.805797+00:00
-- url     : https://prove2.me/submissions/112dab22-a88c-4c07-a7aa-638642739347

import Mathlib
import Theorems.Thm_syracuse_uniform_logarithmic_tail_bound_ge_three

open Filter
open scoped Topology BigOperators

private theorem tail_above (x : ℕ → ℕ) (hinj : Function.Injective x) (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i ≥ N, M < x i := by
  have hs : (x ⁻¹' Set.Iic M).Finite := Set.Finite.preimage hinj.injOn (Set.finite_Iic M)
  obtain ⟨a, ha⟩ := hs.bddAbove
  refine ⟨a+1, Nat.succ_pos _, ?_⟩
  intro i hi
  by_contra h
  have hai : i ≤ a := ha (show i ∈ x ⁻¹' Set.Iic M from Nat.le_of_not_gt h)
  omega

private theorem step_odd (x : ℕ) : Odd (syracuseStep x) := by
  have hn : ¬ 2 ∣ syracuseStep x := Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3*x+1 ≠ 0)
  exact Nat.odd_iff.mpr (by omega)

private theorem orbitMin_after_tail (n M N i : ℕ) (hi : N ≤ i)
    (hTail : ∀ j ≥ N, M < syracuseStep^[j] n) :
    M < syracuseOrbitMin (syracuseStep^[i] n) := by
  let y := syracuseStep^[i] n
  have hm : syracuseOrbitMin y ∈ Set.range (fun j : ℕ => syracuseStep^[j] y) :=
    Nat.sInf_mem (Set.range_nonempty _)
  obtain ⟨j, hj⟩ := hm
  change M < syracuseOrbitMin y
  rw [← hj]
  change M < syracuseStep^[j] (syracuseStep^[i] n)
  rw [← Function.iterate_add_apply]
  exact hTail _ (by omega)

/-- The reciprocal mass of the first L states of an injective Syracuse
orbit is at most an arbitrarily small multiple of log(L+1), up to a constant. -/
theorem syracuse_injective_orbit_reciprocal_sum_sublog (n : ℕ)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n))
    (ε : ℝ) (he : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      (∑ i ∈ Finset.range L, (1:ℝ)/(syracuseStep^[i] n:ℝ)) ≤
        C + ε*Real.log ((L:ℝ)+1) := by
  classical
  let x (i : ℕ) := syracuseStep^[i] n
  let w (i : ℕ) := (1:ℝ)/(x i:ℝ)
  obtain ⟨D,d,hD,hd,hLog⟩ := syracuse_uniform_logarithmic_tail_bound_ge_three
  have hMtop : Tendsto (fun M : ℕ => Real.rpow (Real.log (M:ℝ)) d) atTop atTop :=
    (_root_.tendsto_rpow_atTop hd).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨m,hm⟩ := (tendsto_atTop_atTop.mp hMtop) (D/ε+1)
  let M := max m 3
  have hM : 3 ≤ M := le_max_right _ _
  have hdenom := hm M (le_max_left _ _)
  let δ := D / Real.rpow (Real.log (M:ℝ)) d
  have hpos : 0 < Real.rpow (Real.log (M:ℝ)) d := by
    have h0 : 0 ≤ D/ε := div_nonneg hD.le he.le
    linarith
  have hδ : δ ≤ ε := by
    apply (div_le_iff₀ hpos).mpr
    have hh : D/ε ≤ Real.rpow (Real.log (M:ℝ)) d := by linarith
    have ht := (div_le_iff₀ he).mp hh
    linarith
  obtain ⟨N,hN,hTail⟩ := tail_above x hinj M
  refine ⟨(N:ℝ)+1,by positivity,?_⟩
  intro L hL
  let Z := L+1
  have hZ : 2 ≤ Z := by omega
  have hlog : 0 ≤ Real.log (Z:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z by omega))
  let early := (Finset.range L).filter (fun i => i < N)
  let late := (Finset.range L).filter (fun i => N ≤ i)
  let middle := late.filter (fun i => x i ≤ Z)
  let high := late.filter (fun i => Z < x i)
  have hpart (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
      (∑ i ∈ s, w i) = (∑ i ∈ s.filter P, w i) + ∑ i ∈ s.filter (fun i => ¬P i), w i :=
    (Finset.sum_filter_add_sum_filter_not (s := s) (p := P) (f := w)).symm
  have hsplit : (∑ i ∈ Finset.range L, w i) =
      (∑ i ∈ early, w i) + (∑ i ∈ middle, w i) + ∑ i ∈ high, w i := by
    have h1 := hpart (Finset.range L) (fun i => i < N)
    have h2 := hpart late (fun i => x i ≤ Z)
    simp only [not_lt] at h1
    simp only [not_le] at h2
    change (∑ i ∈ Finset.range L, w i) = (∑ i ∈ early, w i) + (∑ i ∈ late, w i) at h1
    change (∑ i ∈ late, w i) = (∑ i ∈ middle, w i) + (∑ i ∈ high, w i) at h2
    rw [h1,h2,add_assoc]
  have hearly : (∑ i ∈ early, w i) ≤ N := by
    have hsub : early ⊆ Finset.range N := by
      intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    calc
      _ ≤ ∑ i ∈ early, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hz : x i = 0
        · simp [w,hz]
        · have hPos : (0:ℝ) < x i := by exact_mod_cast (Nat.pos_of_ne_zero hz)
          have hcast : (1:ℝ) ≤ x i := by exact_mod_cast (show 1 ≤ x i by omega)
          dsimp [w]
          apply (div_le_iff₀ hPos).mpr
          simpa using hcast
      _ ≤ ∑ i ∈ Finset.range N, (1:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le_one)
      _ = _ := by simp
  have hhigh : (∑ i ∈ high, w i) ≤ 1 := by
    have hsub : high ⊆ Finset.range L := by
      intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    have hZr : (0:ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
    calc
      _ ≤ ∑ i ∈ high, (1:ℝ)/(Z:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hge : (Z:ℝ) ≤ (x i:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hi).2.le
        apply one_div_le_one_div_of_le hZr hge
      _ ≤ ∑ i ∈ Finset.range L, (1:ℝ)/(Z:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (L:ℝ)/(Z:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply (div_le_iff₀ hZr).mpr
        simp [Z]
  let mass := weightedLogMassReal (fun v => 0 < v ∧ Odd v)
    (fun v => (M:ℝ) < (syracuseOrbitMin v:ℝ)) (fun v => 1/(v:ℝ)) (Z:ℝ)
  have hmass : mass ≤ δ := hLog M Z (by exact_mod_cast hM) (by exact_mod_cast hZ)
  let E := (Finset.range (Z+1)).filter
    (fun v => (0 < v ∧ Odd v) ∧ (M:ℝ) < (syracuseOrbitMin v:ℝ))
  have hEmass : (∑ v ∈ E, (1:ℝ)/(v:ℝ)) = mass*Real.log (Z:ℝ) := by
    unfold E mass weightedLogMassReal
    rw [Nat.floor_natCast, Finset.sum_filter]
    have hlogpos : 0 < Real.log (Z:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
    field_simp [hlogpos.ne']
  have himage : middle.image x ⊆ E := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hil,hiZ⟩ := Finset.mem_filter.mp hi
    have hNi := (Finset.mem_filter.mp hil).2
    have himin : M < syracuseOrbitMin (x i) := orbitMin_after_tail n M N i hNi hTail
    have hodd : Odd (x i) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      change Odd (syracuseStep^[j+1] n)
      rw [Function.iterate_succ_apply']
      exact step_odd _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hiZ),
      ⟨⟨by have ht := hTail i hNi; omega,hodd⟩,by exact_mod_cast himin⟩⟩
  have hmiddle : (∑ i ∈ middle, w i) ≤ ε * Real.log (Z:ℝ) := calc
    _ = ∑ v ∈ middle.image x, (1:ℝ)/(v:ℝ) := by rw [Finset.sum_image hinj.injOn]
    _ ≤ ∑ v ∈ E, (1:ℝ)/(v:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
    _ = _ := hEmass
    _ ≤ _ := mul_le_mul_of_nonneg_right (hmass.trans hδ) hlog
  change (∑ i ∈ Finset.range L, w i) ≤ (N:ℝ)+1+ε*Real.log ((L:ℝ)+1)
  rw [hsplit]
  rw [show ((L:ℝ)+1) = (Z:ℝ) by simp [Z]]
  linarith only [hearly,hhigh,hmiddle]

private theorem product_le_exp_reciprocal_sum (n k : ℕ) (hn : 0 < n) :
    (2:ℝ)^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
      (syracuseStep^[k] n : ℝ) ≤
      (3:ℝ)^k*(n:ℝ)*Real.exp ((∑ i ∈ Finset.range k, 1/(syracuseStep^[i] n:ℝ))/3) := by
  let x (i : ℕ) := syracuseStep^[i] n
  let A (i : ℕ) := (Finset.range i).sum fun j => (3*x j+1).factorization 2
  let w (i : ℕ) : ℝ := 1/(x i:ℝ)
  let H (i : ℕ) := ∑ j ∈ Finset.range i, w j
  change (2:ℝ)^(A k)*(x k:ℝ) ≤ 3^k*(n:ℝ)*Real.exp (H k/3)
  induction k with
  | zero => simp [x,A,H]
  | succ k ih =>
    let a := (3*x k+1).factorization 2
    have hA : A (k+1) = A k+a := Finset.sum_range_succ _ _
    have hH : H (k+1) = H k+w k := Finset.sum_range_succ _ _
    have hrow : 2^a*x (k+1) = 3*x k+1 := by
      have hx : x (k+1) = syracuseStep (x k) := Function.iterate_succ_apply' _ _ _
      rw [hx]
      exact Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcast : (2:ℝ)^a*(x (k+1):ℝ) = 3*(x k:ℝ)+1 := by exact_mod_cast hrow
    have hx : (0:ℝ) < x k := by
      have h : 0 < x k := by
        cases k with
        | zero => exact hn
        | succ j =>
          change 0 < syracuseStep^[j+1] n
          rw [Function.iterate_succ_apply']
          exact Nat.ordCompl_pos 2 (by omega)
      exact_mod_cast h
    have hmul : 3+w k ≤ 3*Real.exp (w k/3) := by
      have h := Real.add_one_le_exp (w k/3)
      linarith
    rw [hA, pow_add, mul_assoc,hcast,hH,add_div,Real.exp_add,pow_succ]
    calc
      _ = ((2:ℝ)^(A k)*(x k:ℝ))*(3+w k) := by
        dsimp [w]
        field_simp [hx.ne']
      _ ≤ ((2:ℝ)^(A k)*(x k:ℝ))*(3*Real.exp (w k/3)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      _ ≤ (3^k*(n:ℝ)*Real.exp (H k/3))*(3*Real.exp (w k/3)) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by ring

/-- The affine correction to the product of the pure Syracuse multipliers
is subpower in the length on any injective orbit. -/
theorem syracuse_injective_orbit_product_subpower (n : ℕ) (hn : 0 < n)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n))
    (ε : ℝ) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      (2:ℝ)^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
        (syracuseStep^[k] n : ℝ) ≤ C*(3:ℝ)^k*(((k:ℝ)+1)^ε) := by
  obtain ⟨A,_,hA⟩ := syracuse_injective_orbit_reciprocal_sum_sublog n hinj (3*ε) (by positivity)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨(n:ℝ)*Real.exp (A/3),by positivity,?_⟩
  intro k hk
  let H := ∑ i ∈ Finset.range k, (1:ℝ)/(syracuseStep^[i] n:ℝ)
  have hH : H/3 ≤ A/3+ε*Real.log ((k:ℝ)+1) := by
    have h := hA k hk
    change H ≤ A+3*ε*Real.log ((k:ℝ)+1) at h
    linarith
  calc
    _ ≤ (3:ℝ)^k*(n:ℝ)*Real.exp (H/3) := product_le_exp_reciprocal_sum n k hn
    _ ≤ (3:ℝ)^k*(n:ℝ)*Real.exp (A/3+ε*Real.log ((k:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hH) (by positivity)
    _ = _ := by
      rw [Real.exp_add, Real.rpow_def_of_pos (by positivity : 0 < (k:ℝ)+1)]
      rw [mul_comm ε]
      ring

private theorem weight_bound (x i K : ℕ) (hx : 0 < x) (hle : x ≤ K*(i+1)) :
    (1:ℝ)/((i : ℝ)+1) ≤ K*((1:ℝ)/(x : ℝ)) := by
  have hxq : (0:ℝ) < x := by exact_mod_cast hx
  have hiq : (0:ℝ) < (i:ℝ)+1 := by positivity
  have h := (div_le_div_iff₀ hiq hxq).2 (show (1:ℝ)*(x:ℝ) ≤ (K:ℝ)*((i:ℝ)+1) by
    simpa using (show (x:ℝ) ≤ ((K*(i+1) : ℕ) : ℝ) by exact_mod_cast hle))
  simpa [div_eq_mul_inv, mul_assoc] using h

/-- On an injective Syracuse orbit, times at which the state is at most a
fixed linear function of time have logarithmic density zero. -/
private theorem syracuse_linear_time_sublevel_log_density_zero (n C : ℕ)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    Tendsto (fun L : ℕ =>
      (∑ i ∈ Finset.range L, if syracuseStep^[i] n ≤ C*(i+1) then (1:ℝ)/((i:ℝ)+1) else 0) /
        Real.log ((L:ℝ)+1)) atTop (𝓝 0) := by
  classical
  let x (i : ℕ) := syracuseStep^[i] n
  let K : ℕ := max C 2
  have hK : 2 ≤ K := le_max_right _ _
  have hCK : C ≤ K := le_max_left _ _
  have hKr : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  let good (L : ℕ) := (Finset.range L).filter (fun i => x i ≤ C*(i+1))
  let w (i : ℕ) : ℝ := (1:ℝ)/((i:ℝ)+1)
  let f (L : ℕ) := (∑ i ∈ good L, w i) / Real.log ((L:ℝ)+1)
  have hmatch (L : ℕ) :
      (∑ i ∈ Finset.range L, if syracuseStep^[i] n ≤ C*(i+1) then
        (1:ℝ)/((i:ℝ)+1) else 0) / Real.log ((L:ℝ)+1) = f L := by
    unfold f good w x
    rw [Finset.sum_filter]
  simp_rw [hmatch]
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; positivity
  have hw1 (i : ℕ) : w i ≤ 1 := by
    dsimp [w]
    apply (div_le_iff₀ (by positivity)).mpr
    have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  apply (tendsto_order).mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun L => lt_of_lt_of_le ha
      (div_nonneg (Finset.sum_nonneg (fun i _ => hw i)) (Real.log_nonneg (by have h : (0:ℝ) ≤ L := Nat.cast_nonneg L; linarith))))
  · intro ε he
    obtain ⟨D,d,hD,hd,hLog⟩ := syracuse_uniform_logarithmic_tail_bound_ge_three
    have hMtop : Tendsto (fun M : ℕ => Real.rpow (Real.log (M:ℝ)) d) atTop atTop :=
      (_root_.tendsto_rpow_atTop hd).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    obtain ⟨m, hm⟩ := (tendsto_atTop_atTop.mp hMtop) (4*(K:ℝ)*D/ε+1)
    let M := max m 3
    have hM : 3 ≤ M := le_max_right _ _
    have hdenom := hm M (le_max_left _ _)
    let δ := D / Real.rpow (Real.log (M:ℝ)) d
    have hpos : 0 < Real.rpow (Real.log (M:ℝ)) d := by
      have h0 : 0 ≤ 4*(K:ℝ)*D/ε := by positivity
      linarith
    have hδ : 0 ≤ δ := div_nonneg hD.le hpos.le
    have hδsmall : 2*(K:ℝ)*δ < ε/2 := by
      have hd' : 4*(K:ℝ)*D/ε < Real.rpow (Real.log (M:ℝ)) d := by linarith
      have hh := (div_lt_iff₀ he).mp hd'
      calc
        _ = (2*(K:ℝ)*D) / Real.rpow (Real.log (M:ℝ)) d := by
          dsimp [δ]
          ring
        _ < _ := by apply (div_lt_iff₀ hpos).mpr; nlinarith only [hh]
    obtain ⟨N,hN,hTail⟩ := tail_above x hinj M
    have hLtop : Tendsto (fun L : ℕ => Real.log ((L:ℝ)+1)) atTop atTop :=
      Real.tendsto_log_atTop.comp ((tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    have hev : ∀ᶠ L : ℕ in atTop, 2*(N:ℝ)/ε < Real.log ((L:ℝ)+1) := hLtop.eventually_gt_atTop _
    filter_upwards [eventually_ge_atTop K,hev] with L hKL hlarge
    have hLr : (0:ℝ) < Real.log ((L:ℝ)+1) := by
      have h0 : 0 ≤ 2*(N:ℝ)/ε := by positivity
      linarith
    let Z : ℕ := K*(L+1)
    have hZ : 2 ≤ Z := by
      have h := Nat.mul_le_mul_left K (show 1 ≤ L+1 by omega)
      exact hK.trans (by simpa [Z] using h)
    have hZr : (0:ℝ) < Real.log (Z:ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Z by omega)
    have hlogZ : Real.log (Z:ℝ) ≤ 2*Real.log ((L:ℝ)+1) := by
      have hbound : (K:ℝ) ≤ (L:ℝ)+1 := by exact_mod_cast (hKL.trans (Nat.le_succ L))
      have hlogK := Real.log_le_log hKr hbound
      rw [show (Z:ℝ) = (K:ℝ)*((L:ℝ)+1) by simp [Z], Real.log_mul hKr.ne' (by positivity)]
      linarith
    let small := (good L).filter (fun i => i < N)
    let late := (good L).filter (fun i => N ≤ i)
    have hsum : (∑ i ∈ good L, w i) = (∑ i ∈ small, w i) + ∑ i ∈ late, w i := by
      dsimp [small,late]
      rw [← Finset.sum_filter_add_sum_filter_not (s := good L) (p := fun i => i < N)]
      simp only [not_lt]
    have hsmall : (∑ i ∈ small, w i) ≤ N := by
      have hsubset : small ⊆ Finset.range N := by
        intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      calc
        _ ≤ ∑ i ∈ small, (1:ℝ) := Finset.sum_le_sum (fun i _ => hw1 i)
        _ ≤ ∑ i ∈ Finset.range N, (1:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => zero_le_one)
        _ = _ := by simp
    let mass := weightedLogMassReal (fun v => 0 < v ∧ Odd v)
      (fun v => (M:ℝ) < (syracuseOrbitMin v:ℝ)) (fun v => 1/(v:ℝ)) (Z:ℝ)
    have hmass : mass ≤ δ :=
      hLog M Z (by exact_mod_cast hM) (by exact_mod_cast hZ)
    let E := (Finset.range (Z+1)).filter (fun v => (0 < v ∧ Odd v) ∧ (M:ℝ) < (syracuseOrbitMin v:ℝ))
    have hEmass : (∑ v ∈ E, (1:ℝ)/(v:ℝ)) = mass*Real.log (Z:ℝ) := by
      unfold E mass weightedLogMassReal
      rw [Nat.floor_natCast, Finset.sum_filter]
      field_simp
    have himage : late.image x ⊆ E := by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hi',hNi⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiL,hiC⟩ := Finset.mem_filter.mp hi'
      have hi' := Finset.mem_range.mp hiL
      have hupper : x i ≤ Z :=
        hiC.trans (Nat.mul_le_mul (hCK) (by omega))
      have himin : M < syracuseOrbitMin (x i) := orbitMin_after_tail n M N i hNi hTail
      have hodd : Odd (x i) := by
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        change Odd (syracuseStep^[j+1] n)
        rw [Function.iterate_succ_apply']
        exact step_odd _
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hupper),
        ⟨⟨by have ht := hTail i hNi; omega,hodd⟩,by exact_mod_cast himin⟩⟩
    have hlate : (∑ i ∈ late, w i) ≤ (K:ℝ)*δ*Real.log (Z:ℝ) := calc
      _ ≤ ∑ i ∈ late, (K:ℝ)*((1:ℝ)/(x i:ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hi',hNi⟩ := Finset.mem_filter.mp hi
        obtain ⟨_,hCi⟩ := Finset.mem_filter.mp hi'
        have hxPos : 0 < x i := by have ht := hTail i hNi; omega
        exact weight_bound _ _ _ hxPos (hCi.trans (Nat.mul_le_mul_right _ hCK))
      _ = (K:ℝ)*∑ v ∈ late.image x, (1:ℝ)/(v:ℝ) := by
        rw [Finset.sum_image hinj.injOn, Finset.mul_sum]
      _ ≤ (K:ℝ)*∑ v ∈ E, (1:ℝ)/(v:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hKr.le
        exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
      _ = (K:ℝ)*mass*Real.log (Z:ℝ) := by rw [hEmass]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hKr.le) hZr.le
    have hsumUpper : (∑ i ∈ good L, w i) ≤ (N:ℝ)+(K:ℝ)*δ*Real.log (Z:ℝ) := by
      rw [hsum]
      linarith only [hsmall,hlate]
    have hNsmall : (N:ℝ) < (ε/2)*Real.log ((L:ℝ)+1) := by
      have hh := (div_lt_iff₀ he).mp hlarge
      nlinarith only [hh]
    have htwo : (K:ℝ)*δ*Real.log (Z:ℝ) < (ε/2)*Real.log ((L:ℝ)+1) := calc
      _ ≤ (K:ℝ)*δ*(2*Real.log ((L:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hlogZ (mul_nonneg hKr.le hδ)
      _ = (2*(K:ℝ)*δ)*Real.log ((L:ℝ)+1) := by ring
      _ < _ := mul_lt_mul_of_pos_right hδsmall hLr
    apply (div_lt_iff₀ hLr).mpr
    linarith only [hsumUpper,hNsmall,htwo]

/-- Every fixed coefficient strictly less than one gives a zero-log-density
exceptional set for the cumulative valuation deficit on an injective orbit. -/
theorem solution
    (n : ℕ) (hn : 0 < n) (q D : ℝ) (hq : q < 1)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    Tendsto (fun L : ℕ =>
      (∑ k ∈ Finset.range L,
        if 0 < k ∧ (3:ℝ)^k ≤ D*(2:ℝ)^((Finset.range k).sum fun i =>
          (3*syracuseStep^[i] n+1).factorization 2)*(((k:ℝ)+1)^q)
        then (1:ℝ)/((k:ℝ)+1) else 0) / Real.log ((L:ℝ)+1)) atTop (𝓝 0) := by
  classical
  let x (k : ℕ) := syracuseStep^[k] n
  let A (k : ℕ) := (Finset.range k).sum fun i => (3*x i+1).factorization 2
  let S (k : ℕ) : Prop := 0 < k ∧ (3:ℝ)^k ≤ D*(2:ℝ)^(A k)*(((k:ℝ)+1)^q)
  obtain ⟨R,hR,hprod⟩ := syracuse_injective_orbit_product_subpower n hn hinj (1-q) (by linarith)
  obtain ⟨C,hC⟩ := exists_nat_ge (R*D)
  have hlinear (k : ℕ) (hs : S k) : syracuseStep^[k] n ≤ C*(k+1) := by
    have hp : (2:ℝ)^(A k)*(x k:ℝ) ≤ R*(3:ℝ)^k*(((k:ℝ)+1)^(1-q)) :=
      hprod k (Nat.succ_le_of_lt hs.1)
    have hqpos : 0 < (k:ℝ)+1 := by positivity
    have hx : (x k : ℝ) ≤ (C:ℝ)*((k:ℝ)+1) := by
      apply le_of_mul_le_mul_left _ (by positivity : (0:ℝ) < 2^(A k))
      calc
        _ ≤ R*(3:ℝ)^k*(((k:ℝ)+1)^(1-q)) := hp
        _ ≤ R*(D*(2:ℝ)^(A k)*(((k:ℝ)+1)^q))*(((k:ℝ)+1)^(1-q)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2 hR.le) (by positivity)
        _ = (R*D)*(2:ℝ)^(A k)*(((k:ℝ)+1)^q*(((k:ℝ)+1)^(1-q))) := by ring
        _ = (R*D)*(2:ℝ)^(A k)*((k:ℝ)+1) := by
          rw [← Real.rpow_add hqpos, show q+(1-q)=1 by ring, Real.rpow_one]
        _ ≤ (C:ℝ)*(2:ℝ)^(A k)*((k:ℝ)+1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (by positivity)
        _ = _ := by ring
    exact_mod_cast hx
  have htend := syracuse_linear_time_sublevel_log_density_zero n C hinj
  let F (L : ℕ) :=
    (∑ k ∈ Finset.range L, if S k then (1:ℝ)/((k:ℝ)+1) else 0)/Real.log ((L:ℝ)+1)
  change Tendsto F atTop (𝓝 0)
  refine tendsto_order.mpr ⟨?_,?_⟩
  · intro a ha
    exact Eventually.of_forall (fun L => lt_of_lt_of_le ha (by
      apply div_nonneg
      · exact Finset.sum_nonneg (fun k _ => by split <;> positivity)
      · apply Real.log_nonneg
        have h : (0:ℝ) ≤ L := Nat.cast_nonneg _
        linarith))
  · intro a ha
    filter_upwards [(tendsto_order.mp htend).2 a ha] with L hL
    apply lt_of_le_of_lt _ hL
    apply div_le_div_of_nonneg_right
    · apply Finset.sum_le_sum
      intro k _
      by_cases hs : S k
      · simp [hs,hlinear k hs]
      · simp only [if_neg hs]
        split <;> positivity
    · apply Real.log_nonneg
      have h : (0:ℝ) ≤ L := Nat.cast_nonneg _
      linarith
