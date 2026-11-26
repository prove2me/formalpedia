-- Prove2me | solution 1 for syracuse_small_valuation_deficit_times_log_density_zero
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:00:57.176824+00:00
-- url     : https://prove2.me/submissions/36e11aa4-d803-4e61-9b4f-2316017b9fdc

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

private theorem odd_state_product (s : Finset ℕ) (b : ℕ)
    (hf : ∀ x ∈ s, b + 2 ≤ x) (ho : ∀ x ∈ s, x % 2 = 1) :
    b * (∏ x ∈ s, x) ≤ (b + 2 * s.card) * (∏ x ∈ s, (x - 2)) := by
  induction s using Finset.strongInductionOn generalizing b with
  | _ s ih =>
    by_cases h : s.Nonempty
    · let a := s.min' h
      have ha : a ∈ s := Finset.min'_mem _ _
      have hfa := hf a ha
      let rest := s.erase a
      have hproper : rest ⊂ s := Finset.erase_ssubset ha
      have hrest : ∀ x ∈ rest, a+2 ≤ x := by
        intro x hx
        have hax := Finset.min'_lt_of_mem_erase_min' s h hx
        have hox := ho x (hproper.subset hx)
        have hoa := ho a ha
        omega
      have ih' := ih rest hproper a hrest (fun x hx => ho x (hproper.subset hx))
      have hins : insert a rest = s := Finset.insert_erase ha
      have hnot : a ∉ rest := Finset.notMem_erase a s
      rw [← hins, Finset.card_insert_of_notMem hnot, Finset.prod_insert hnot, Finset.prod_insert hnot]
      have hc : b * (a + 2*rest.card) ≤ (b+2*(rest.card+1))*(a-2) := calc
        _ = b*(a-2)+b*(2*(rest.card+1)) := by
          have he : a + 2*rest.card = (a-2)+2*(rest.card+1) := by omega
          rw [he, Nat.mul_add]
        _ ≤ b*(a-2)+(a-2)*(2*(rest.card+1)) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
        _ = _ := by ring
      calc
        _ = b * (a * (∏ x ∈ rest, x)) := rfl
        _ ≤ b * ((a + 2 * rest.card) * (∏ x ∈ rest, (x-2))) :=
          Nat.mul_le_mul_left _ ih'
        _ = (b * (a+2*rest.card)) * (∏ x ∈ rest, (x-2)) := by ring
        _ ≤ ((b+2*(rest.card+1))*(a-2)) * (∏ x ∈ rest, (x-2)) :=
          Nat.mul_le_mul_right _ hc
        _ = _ := by ring
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]

private theorem local_sixth_power (x : ℕ) (hx : 2 ≤ x) :
    (x-2)*(3*x+1)^6 ≤ 3^6*x^6*x := by
  have cubic : (x-1)*(3*x+1)^3 ≤ (3*x)^3*x := by
    obtain ⟨u, hu⟩ : ∃ u : ℕ, x = u + 1 := ⟨x-1,by omega⟩
    have hnat : (x-1)*(3*x+1)^3 + (18*x^2+8*x+1) = (3*x)^3*x := by
      rw [hu, Nat.add_sub_cancel]
      ring
    omega
  have square : (x-2)*x ≤ (x-1)^2 := by
    obtain ⟨u, hu⟩ : ∃ u : ℕ, x = u+2 := ⟨x-2,by omega⟩
    have hnat : (x-2)*x+1 = (x-1)^2 := by
      rw [hu, Nat.add_sub_cancel, show u+2-1=u+1 by omega]
      ring
    omega
  have hsq := Nat.pow_le_pow_left cubic 2
  have he : 0 < (x-1)^2 := Nat.pow_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ he
  calc
    _ = ((x-1)*(3*x+1)^3)^2*(x-2) := by ring
    _ ≤ ((3*x)^3*x)^2*(x-2) := Nat.mul_le_mul_right _ hsq
    _ = (3*x)^6*x*((x-2)*x) := by ring
    _ ≤ (3*x)^6*x*(x-1)^2 := Nat.mul_le_mul_left _ square
    _ = _ := by ring

/-- A bound on the valuation sum of a Syracuse prefix with no repeated states.
The factor comparing the prefix to the pure multiplier (3^k/2^{A_k}) grows
polynomially with its length. -/
private theorem syracuse_distinct_prefix_valuation_bound (n b k : ℕ)
    (hodd : n % 2 = 1) (hfloor : ∀ i < k, b+2 ≤ syracuseStep^[i] n)
    (huniq : Set.InjOn (fun i : ℕ => syracuseStep^[i] n) {i | i < k}) :
    b * 2^(6 * ((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2)) *
      (syracuseStep^[k] n)^6 ≤ 3^(6*k) * n^6 * (b+2*k) := by
  by_cases hb : b = 0
  · simp [hb]
  let x (i : ℕ) := syracuseStep^[i] n
  let A (j : ℕ) := (Finset.range j).sum fun i => (3*x i+1).factorization 2
  let P (j : ℕ) := ∏ i ∈ Finset.range j, x i
  let Q (j : ℕ) := ∏ i ∈ Finset.range j, (x i-2)
  have hprod (j : ℕ) (hj : j ≤ k) :
      Q j * 2^(6*A j) * (x j)^6 ≤ 3^(6*j)*n^6*P j := by
    induction j with
    | zero => simp [A,P,Q,x]
    | succ j ih =>
      have hjk : j < k := by omega
      let a := (3*x j+1).factorization 2
      have hx : 2^a*x (j+1) = 3*x j+1 := by
        have hnext : x (j+1) = syracuseStep (x j) := Function.iterate_succ_apply' _ _ _
        rw [hnext]
        exact Nat.ordProj_mul_ordCompl_eq_self _ _
      have hA : A (j+1) = A j + a := Finset.sum_range_succ _ _
      have hP : P (j+1) = P j * x j := Finset.prod_range_succ _ _
      have hQ : Q (j+1) = Q j * (x j-2) := Finset.prod_range_succ _ _
      have hpow : (2^a*x (j+1))^6 = 2^(6*a) * (x (j+1))^6 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm a 6]
      have hlocal : (x j-2)*(2^(6*a)*(x (j+1))^6) ≤ 3^6*(x j)^6*x j := by
        rw [← hpow,hx]
        exact local_sixth_power _ (by have hf : b + 2 ≤ x j := hfloor j hjk; omega)
      rw [hA,hP,hQ, Nat.mul_add, pow_add 2 (6*A j) (6*a),
        show 6*(j+1) = 6*j+6 by omega, pow_add 3 (6*j) 6]
      calc
        _ = (Q j * 2^(6*A j)) * ((x j-2)*(2^(6*a)*(x (j+1))^6)) := by ring
        _ ≤ (Q j * 2^(6*A j)) * (3^6*(x j)^6*x j) := Nat.mul_le_mul_left _ hlocal
        _ = (Q j * 2^(6*A j) * (x j)^6) * (3^6*x j) := by ring
        _ ≤ (3^(6*j)*n^6*P j) * (3^6*x j) := Nat.mul_le_mul_right _ (ih (by omega))
        _ = _ := by ring
  have hi : Set.InjOn x (↑(Finset.range k) : Set ℕ) := by
    intro i hi j hj hij
    exact huniq (by simpa using hi) (by simpa using hj) hij
  let seen := (Finset.range k).image x
  have hc : seen.card = k := (Finset.card_image_of_injOn hi).trans (Finset.card_range k)
  have hp : (∏ y ∈ seen, y) = P k := Finset.prod_image hi
  have hq : (∏ y ∈ seen, (y-2)) = Q k := Finset.prod_image hi
  have hseen (y : ℕ) (hy : y ∈ seen) : ∃ i < k, x i = y := by
    obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i,Finset.mem_range.mp hi',rfl⟩
  have he := odd_state_product seen b
    (fun y hy => by obtain ⟨i,hi',rfl⟩ := hseen y hy; exact hfloor i hi')
    (fun y hy => by
      obtain ⟨i,_,rfl⟩ := hseen y hy
      cases i with
      | zero => exact hodd
      | succ i =>
        change syracuseStep^[i+1] n % 2 = 1
        rw [Function.iterate_succ_apply']
        have hnd := Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3*x i+1 ≠ 0)
        change ¬ 2 ∣ syracuseStep (x i) at hnd
        change syracuseStep (x i) % 2 = 1
        omega)
  rw [hc,hp,hq] at he
  have hpositive : 0 < Q k := by
    apply Finset.prod_pos
    intro i hi'
    have hf : b+2 ≤ x i := hfloor i (Finset.mem_range.mp hi')
    omega
  apply Nat.le_of_mul_le_mul_right _ hpositive
  change (b*2^(6*A k)*(x k)^6)*Q k ≤ (3^(6*k)*n^6*(b+2*k))*Q k
  calc
    _ = b*(Q k*2^(6*A k)*(x k)^6) := by ring
    _ ≤ b*(3^(6*k)*n^6*P k) := Nat.mul_le_mul_left _ (hprod k le_rfl)
    _ = (3^(6*k)*n^6)*(b*P k) := by ring
    _ ≤ (3^(6*k)*n^6)*((b+2*k)*Q k) := Nat.mul_le_mul_left _ he
    _ = _ := by ring

/-- On an injective odd Syracuse orbit, times at which the cumulative
valuation deficit is at most `(5/6) log₂(k+1)` plus a fixed constant have
logarithmic density zero. -/
theorem solution (n D : ℕ)
    (hodd : n % 2 = 1) (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    Tendsto (fun L : ℕ =>
      (∑ k ∈ Finset.range L,
        if 3^(6*k) ≤ D * 2^(6*((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2)) *
          (k+1)^5 then (1:ℝ)/((k:ℝ)+1) else 0) / Real.log ((L:ℝ)+1)) atTop (𝓝 0) := by
  classical
  let x (k : ℕ) := syracuseStep^[k] n
  let A (k : ℕ) := (Finset.range k).sum fun i => (3*x i+1).factorization 2
  let S (k : ℕ) : Prop := 3^(6*k) ≤ D*2^(6*A k)*(k+1)^5
  let C : ℕ := (2*(D+1))*n
  have hxge (i : ℕ) : 3 ≤ x i := by
    have ho : x i % 2 = 1 := by
      cases i with
      | zero => exact hodd
      | succ j =>
        change syracuseStep^[j+1] n % 2 = 1
        rw [Function.iterate_succ_apply']
        exact Nat.odd_iff.mp (step_odd _)
    have hno : x i ≠ 1 := by
      intro he
      have hone : syracuseStep 1 = 1 := by decide +kernel
      have hnext : x (i+1) = syracuseStep (x i) := Function.iterate_succ_apply' _ _ _
      have h := hinj (show x (i+1) = x i from hnext.trans (he ▸ hone) |>.trans he.symm)
      omega
    omega
  have hpow : 2*D ≤ (2*(D+1))^6 := calc
    _ ≤ 2*(D+1) := by omega
    _ ≤ _ := Nat.le_self_pow (by decide) _
  have hlinear (k : ℕ) (hS : S k) : x k ≤ C*(k+1) := by
    have hbudget : 2^(6*A k)*(x k)^6 ≤ 3^(6*k)*n^6*(1+2*k) := by
      simpa only [one_mul] using
        syracuse_distinct_prefix_valuation_bound n 1 k hodd (fun i _ => hxge i) hinj.injOn
    have ht : (x k)^6 ≤ (C*(k+1))^6 := by
      have hpos : 0 < (2:ℕ)^(6*A k) := Nat.two_pow_pos _
      apply Nat.le_of_mul_le_mul_left _ hpos
      calc
        _ ≤ 3^(6*k)*n^6*(1+2*k) := hbudget
        _ ≤ (D*2^(6*A k)*(k+1)^5)*n^6*(1+2*k) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hS)
        _ ≤ (D*2^(6*A k)*(k+1)^5)*n^6*(2*(k+1)) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = (2^(6*A k)*n^6*(k+1)^6)*(2*D) := by ring
        _ ≤ (2^(6*A k)*n^6*(k+1)^6)*(2*(D+1))^6 := Nat.mul_le_mul_left _ hpow
        _ = _ := by dsimp [C]; ring
    exact (Nat.pow_le_pow_iff_left (by decide : 6 ≠ 0)).mp ht
  have htend := syracuse_linear_time_sublevel_log_density_zero n C hinj
  let F (L : ℕ) :=
    (∑ k ∈ Finset.range L, if S k then (1:ℝ)/((k:ℝ)+1) else 0) / Real.log ((L:ℝ)+1)
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
      · have hb : syracuseStep^[k] n ≤ C*(k+1) := hlinear k hs
        simp [hs,hb]
      · simp only [if_neg hs]
        split <;> positivity
    · apply Real.log_nonneg
      have h : (0:ℝ) ≤ L := Nat.cast_nonneg _
      linarith
