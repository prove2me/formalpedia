-- Prove2me | solution 1 for cosine_sublevel_density
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:23:57.631167+00:00
-- url     : https://prove2.me/submissions/ac0ceea4-085d-46f0-a101-1e7f13ab4595

import Mathlib
open MeasureTheory Filter
open scoped ENNReal

/-- Auxiliary lemma: the cosine sublevel density bound for nonnegative `K`.
The sublevel set `{u | m * (1 - cos (u * y)) ≤ K}` meets each period in two
arcs of total length `4 * arcsin (√(K / (2m))) / y`; covering `[0, U]` by
`⌊Uy / (2π)⌋₊ + 2` such arcs gives the density bound. -/
lemma aux_cosine_sublevel (K : ℝ) (hK : 0 ≤ K) (ρ : ℝ≥0∞) (hρ : 0 < ρ) (hρtop : ρ ≠ ⊤) :
    ∃ M : ℝ, ∀ m y : ℝ, M ≤ m → 0 < y → ∃ U0 : ℝ, ∀ U : ℝ, U0 ≤ U →
      (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if m * (1 - Real.cos (u * y)) ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ρ := by
  set δ := ρ.toReal / 2 with hδdef
  have hδpos : 0 < δ := by
    have h := ENNReal.toReal_pos hρ.ne' hρtop
    rw [hδdef]
    linarith
  set ε' := min (Real.pi * δ / 2) (Real.pi / 2) with hε'def
  have hε'pos : 0 < ε' := by
    rw [hε'def]
    refine lt_min ?_ ?_
    · have h := mul_pos Real.pi_pos hδpos
      linarith
    · linarith [Real.pi_pos]
  have hε'le1 : ε' ≤ Real.pi / 2 := by
    rw [hε'def]
    exact min_le_right _ _
  have hε'le2 : ε' ≤ Real.pi * δ / 2 := by
    rw [hε'def]
    exact min_le_left _ _
  have hε'ltπ : ε' < Real.pi := lt_of_le_of_lt hε'le1 (by linarith [Real.pi_pos])
  have hsinε' : 0 < Real.sin ε' := Real.sin_pos_of_pos_of_lt_pi hε'pos hε'ltπ
  refine ⟨max (max (K / 2) (K / (2 * (Real.sin ε') ^ 2))) 1, fun m y hm hy => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hmK2 : K / 2 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmK3 : K / (2 * (Real.sin ε') ^ 2) ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmpos : (0 : ℝ) < m := by linarith
  have h2m : (0 : ℝ) < 2 * m := by linarith
  set s := √(K / (2 * m)) with hsdef
  set a := Real.arcsin s with hadef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show K / (2 * m) ≤ 1 from (div_le_one h2m).mpr (by linarith [hmK2]))
    rwa [Real.sqrt_one] at h
  have hs_sin : s ≤ Real.sin ε' := by
    have hKm : K / (2 * m) ≤ (Real.sin ε') ^ 2 := by
      have hsin2 : (0 : ℝ) < 2 * (Real.sin ε') ^ 2 := by
        have h := pow_pos hsinε' 2
        linarith
      have h1 : K ≤ m * (2 * (Real.sin ε') ^ 2) := (div_le_iff₀ hsin2).mp hmK3
      rw [div_le_iff₀ h2m]
      have e : (Real.sin ε') ^ 2 * (2 * m) = m * (2 * (Real.sin ε') ^ 2) := by ring
      rw [e]
      exact h1
    have h := Real.sqrt_le_sqrt hKm
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos hsinε'] at h
  have haε : a ≤ ε' := by
    have h := Real.arcsin_le_arcsin hs_sin
    rwa [Real.arcsin_sin (by linarith [hε'pos, Real.pi_pos] : -(Real.pi / 2) ≤ ε') hε'le1] at h
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have haπ : a ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
  have haδ : 2 * a / Real.pi ≤ δ := by
    rw [div_le_iff₀ Real.pi_pos]
    have h2 : 2 * a ≤ Real.pi * δ := by linarith [haε, hε'le2]
    linarith
  refine ⟨max 1 (8 * a / (y * δ)), fun U hU => ?_⟩
  have hU1 : (1 : ℝ) ≤ U := le_trans (le_max_left _ _) hU
  have hUpos : (0 : ℝ) < U := by linarith
  have hUge : 8 * a / (y * δ) ≤ U := le_trans (le_max_right _ _) hU
  have hU2 : 8 * a / (U * y) ≤ δ := by
    have h1 : 8 * a ≤ U * (y * δ) := (div_le_iff₀ (mul_pos hy hδpos)).mp hUge
    rw [div_le_iff₀ (mul_pos hUpos hy)]
    have e : δ * (U * y) = U * (y * δ) := by ring
    rw [e]
    exact h1
  set A : Set ℝ := {u | m * (1 - Real.cos (u * y)) ≤ K} with hAdef
  have hA : MeasurableSet A := by
    have hf : Measurable (fun u => m * (1 - Real.cos (u * y))) :=
      ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).measurable).const_sub 1 |>.const_mul m
    exact measurableSet_le hf measurable_const
  have hfun : (fun u => ENNReal.ofReal (if m * (1 - Real.cos (u * y)) ≤ K then (1 : ℝ) else 0))
      = A.indicator 1 := by
    funext u
    by_cases h : m * (1 - Real.cos (u * y)) ≤ K
    · have hu : u ∈ A := h
      simp [Set.indicator_of_mem hu, h]
    · have hu : u ∉ A := h
      simp [Set.indicator_of_notMem hu, h]
  have step1 : (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if m * (1 - Real.cos (u * y)) ≤ K then (1 : ℝ) else 0) ∂volume)
      = volume (A ∩ Set.Icc 0 U) := by
    rw [hfun, lintegral_indicator_one hA, Measure.restrict_apply hA]
  have hcover : A ∩ Set.Icc 0 U ⊆ ⋃ k ∈ Finset.Icc (0 : ℤ) ((⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 1),
      Set.Icc ((2 * Real.pi * (k : ℝ) - 2 * a) / y) ((2 * Real.pi * (k : ℝ) + 2 * a) / y) := by
    intro u hu
    obtain ⟨huA, huI⟩ := hu
    have huA' : m * (1 - Real.cos (u * y)) ≤ K := huA
    have hu0 : (0 : ℝ) ≤ u := huI.1
    have huU : u ≤ U := huI.2
    have huy : (0 : ℝ) ≤ u * y := mul_nonneg hu0 hy.le
    have huyU : u * y ≤ U * y := mul_le_mul_of_nonneg_right huU hy.le
    have h1cos : 1 - Real.cos (u * y) = 2 * Real.sin (u * y / 2) ^ 2 := by
      have h1 := Real.cos_two_mul (u * y / 2)
      have h2 : 2 * (u * y / 2) = u * y := by ring
      rw [h2] at h1
      have h3 := Real.sin_sq_add_cos_sq (u * y / 2)
      linarith
    have hsq : Real.sin (u * y / 2) ^ 2 ≤ K / (2 * m) := by
      rw [le_div_iff₀ h2m]
      have h := huA'
      rw [h1cos] at h
      have e : Real.sin (u * y / 2) ^ 2 * (2 * m) = m * (2 * Real.sin (u * y / 2) ^ 2) := by ring
      rw [e]
      exact h
    have hsin : |Real.sin (u * y / 2)| ≤ s := by
      have e : |Real.sin (u * y / 2)| = √(Real.sin (u * y / 2) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      rw [e]
      exact Real.sqrt_le_sqrt hsq
    set k : ℤ := round (u * y / (2 * Real.pi)) with hkdef
    have hr : |u * y / (2 * Real.pi) - (k : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hφabs : |u * y / 2 - (k : ℝ) * Real.pi| ≤ Real.pi / 2 := by
      have e1 : u * y / 2 - (k : ℝ) * Real.pi = (u * y / (2 * Real.pi) - (k : ℝ)) * Real.pi := by
        field_simp
      rw [e1, abs_mul, abs_of_pos Real.pi_pos]
      calc |u * y / (2 * Real.pi) - (k : ℝ)| * Real.pi ≤ (1 / 2) * Real.pi :=
            mul_le_mul_of_nonneg_right hr Real.pi_pos.le
        _ = Real.pi / 2 := by ring
    have hsinφ : |Real.sin (u * y / 2 - (k : ℝ) * Real.pi)| = |Real.sin (u * y / 2)| := by
      have e : Real.sin (u * y / 2 - (k : ℝ) * Real.pi)
          = (-1 : ℝ) ^ k * Real.sin (u * y / 2) := by
        rw [Real.sin_sub, Real.cos_int_mul_pi, Real.sin_int_mul_pi]
        ring
      rw [e]
      simp [abs_mul, abs_pow]
    have hφle : |u * y / 2 - (k : ℝ) * Real.pi| ≤ a := by
      have h1 : |u * y / 2 - (k : ℝ) * Real.pi|
          = Real.arcsin (Real.sin |u * y / 2 - (k : ℝ) * Real.pi|) := by
        rw [Real.arcsin_sin (by
          have h := abs_nonneg (u * y / 2 - (k : ℝ) * Real.pi)
          linarith [Real.pi_pos]) hφabs]
      rw [h1]
      refine Real.arcsin_le_arcsin ?_
      have hsinabs : Real.sin |u * y / 2 - (k : ℝ) * Real.pi|
          = |Real.sin (u * y / 2 - (k : ℝ) * Real.pi)| := by
        by_cases hφ : (0 : ℝ) ≤ u * y / 2 - (k : ℝ) * Real.pi
        · have hle : u * y / 2 - (k : ℝ) * Real.pi ≤ Real.pi := by
            have h := le_abs_self (u * y / 2 - (k : ℝ) * Real.pi)
            linarith [hφabs, Real.pi_pos]
          rw [abs_of_nonneg hφ, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hφ hle)]
        · have hφ2 : (0 : ℝ) ≤ -(u * y / 2 - (k : ℝ) * Real.pi) := by linarith
          have hle : -(u * y / 2 - (k : ℝ) * Real.pi) ≤ Real.pi := by
            have h := neg_le_abs (u * y / 2 - (k : ℝ) * Real.pi)
            linarith [hφabs, Real.pi_pos]
          have hsinn : Real.sin (u * y / 2 - (k : ℝ) * Real.pi) ≤ 0 := by
            have h := Real.sin_nonneg_of_nonneg_of_le_pi hφ2 hle
            rw [Real.sin_neg] at h
            linarith
          rw [abs_of_neg (lt_of_not_ge hφ), abs_of_nonpos hsinn, Real.sin_neg]
      rw [hsinabs, hsinφ]
      exact hsin
    have habs : |u * y - 2 * Real.pi * (k : ℝ)| ≤ 2 * a := by
      have e : u * y - 2 * Real.pi * (k : ℝ) = 2 * (u * y / 2 - (k : ℝ) * Real.pi) := by ring
      rw [e, abs_mul]
      have h2 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
      rw [h2]
      exact mul_le_mul_of_nonneg_left hφle (by norm_num)
    have habs' := abs_le.mp habs
    have hk0 : 0 ≤ k := by
      have h2πk : -Real.pi ≤ 2 * Real.pi * (k : ℝ) := by linarith [habs'.2, huy, haπ]
      have hk1 : (-1 : ℝ) < (k : ℝ) := by
        by_contra hc
        push_neg at hc
        have hle : 2 * Real.pi * (k : ℝ) ≤ 2 * Real.pi * (-1) :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) Real.pi_pos.le)
        linarith [Real.pi_pos, hle, h2πk]
      have hki : (-1 : ℤ) < k := by exact_mod_cast hk1
      omega
    have hkN : k ≤ (⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 1 := by
      have h2πk : 2 * Real.pi * (k : ℝ) ≤ U * y + Real.pi := by linarith [habs'.1, huyU, haπ]
      have hkx : (k : ℝ) ≤ U * y / (2 * Real.pi) + 1 / 2 := by
        have hπ2 : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
        have e : (U * y + Real.pi) / (2 * Real.pi) = U * y / (2 * Real.pi) + 1 / 2 := by
          field_simp
        rw [← e, le_div_iff₀ hπ2]
        have e2 : (k : ℝ) * (2 * Real.pi) = 2 * Real.pi * (k : ℝ) := by ring
        rw [e2]
        exact h2πk
      by_contra hlt
      push_neg at hlt
      have h2 : (⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 2 ≤ k := by omega
      have h3 : (⌊U * y / (2 * Real.pi)⌋₊ : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast h2
      have h4 : U * y / (2 * Real.pi) < (⌊U * y / (2 * Real.pi)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith [hkx, h3, h4]
    refine Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hk0, hkN⟩) ⟨?_, ?_⟩
    · rw [div_le_iff₀ hy]
      linarith [habs'.1]
    · rw [le_div_iff₀ hy]
      linarith [habs'.2]
  have hcard : (Finset.Icc (0 : ℤ) ((⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 1)).card
      = ⌊U * y / (2 * Real.pi)⌋₊ + 2 := by
    rw [Int.card_Icc]
    have e : ((⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 1 + 1 - 0)
        = ((⌊U * y / (2 * Real.pi)⌋₊ + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e, Int.toNat_natCast]
  have hvol : volume (A ∩ Set.Icc 0 U)
      ≤ ENNReal.ofReal ((U * y / (2 * Real.pi) + 2) * (4 * a / y)) := by
    calc volume (A ∩ Set.Icc 0 U)
        ≤ volume (⋃ k ∈ Finset.Icc (0 : ℤ) ((⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 1),
            Set.Icc ((2 * Real.pi * (k : ℝ) - 2 * a) / y) ((2 * Real.pi * (k : ℝ) + 2 * a) / y)) :=
          measure_mono hcover
      _ ≤ ∑ k ∈ Finset.Icc (0 : ℤ) ((⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 1),
            volume (Set.Icc ((2 * Real.pi * (k : ℝ) - 2 * a) / y) ((2 * Real.pi * (k : ℝ) + 2 * a) / y)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ k ∈ Finset.Icc (0 : ℤ) ((⌊U * y / (2 * Real.pi)⌋₊ : ℤ) + 1),
            ENNReal.ofReal (4 * a / y) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Real.volume_Icc]
          congr 1
          rw [← sub_div]
          congr 1
          ring
      _ = (⌊U * y / (2 * Real.pi)⌋₊ + 2) • ENNReal.ofReal (4 * a / y) := by
          rw [Finset.sum_const, hcard]
      _ ≤ ENNReal.ofReal ((U * y / (2 * Real.pi) + 2) * (4 * a / y)) := by
          rw [nsmul_eq_mul]
          have hnn : (0 : ℝ) ≤ U * y / (2 * Real.pi) :=
            div_nonneg (mul_nonneg (by linarith) hy.le) (by linarith [Real.pi_pos])
          have hfl : (⌊U * y / (2 * Real.pi)⌋₊ : ℝ) ≤ U * y / (2 * Real.pi) := Nat.floor_le hnn
          have hcast : ((⌊U * y / (2 * Real.pi)⌋₊ + 2 : ℕ) : ℝ≥0∞)
              ≤ ENNReal.ofReal (U * y / (2 * Real.pi) + 2) := by
            rw [← ENNReal.ofReal_natCast]
            refine ENNReal.ofReal_le_ofReal ?_
            push_cast
            linarith [hfl]
          calc ((⌊U * y / (2 * Real.pi)⌋₊ + 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (4 * a / y)
              ≤ ENNReal.ofReal (U * y / (2 * Real.pi) + 2) * ENNReal.ofReal (4 * a / y) :=
                mul_le_mul hcast le_rfl bot_le bot_le
            _ = ENNReal.ofReal ((U * y / (2 * Real.pi) + 2) * (4 * a / y)) :=
                (ENNReal.ofReal_mul (by linarith [hnn])).symm
  calc (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if m * (1 - Real.cos (u * y)) ≤ K then (1 : ℝ) else 0) ∂volume) * (ENNReal.ofReal U)⁻¹
      = volume (A ∩ Set.Icc 0 U) * (ENNReal.ofReal U)⁻¹ := by rw [step1]
    _ ≤ ENNReal.ofReal ((U * y / (2 * Real.pi) + 2) * (4 * a / y)) * (ENNReal.ofReal U)⁻¹ :=
        mul_le_mul hvol le_rfl bot_le bot_le
    _ = ENNReal.ofReal (2 * a / Real.pi + 8 * a / (U * y)) := by
        have hP : (U * y / (2 * Real.pi) + 2) * (4 * a / y)
            = (2 * a / Real.pi + 8 * a / (U * y)) * U := by
          field_simp [Real.pi_ne_zero, hy.ne', hUpos.ne']
          ring
        have hnn : (0 : ℝ) ≤ 2 * a / Real.pi + 8 * a / (U * y) :=
          add_nonneg (div_nonneg (by linarith [ha0]) Real.pi_pos.le)
            (div_nonneg (by linarith [ha0]) (mul_nonneg hUpos.le hy.le))
        rw [hP, ENNReal.ofReal_mul hnn, mul_assoc,
          ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hUpos).ne' ENNReal.ofReal_ne_top, mul_one]
    _ ≤ ρ := by
        rw [← ENNReal.ofReal_toReal hρtop]
        refine ENNReal.ofReal_le_ofReal ?_
        have hρt : ρ.toReal = 2 * δ := by
          rw [hδdef]
          ring
        linarith [haδ, hU2, hρt]

theorem solution :
  ∀ K : Real, ∀ ρ : ENNReal, 0 < ρ →
    ∃ M : Real, ∀ m y : Real, M ≤ m → 0 < y →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if m * (1 - Real.cos (u * y)) ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ρ := by
  intro K ρ hρ
  rcases eq_or_ne ρ ⊤ with rfl | hρtop
  · exact ⟨1, fun m y _ _ => ⟨1, fun U _ => le_top⟩⟩
  · obtain ⟨M, hM⟩ := aux_cosine_sublevel (max K 0) (le_max_right K 0) ρ hρ hρtop
    refine ⟨M, fun m y hm hy => ?_⟩
    obtain ⟨U0, hU0⟩ := hM m y hm hy
    refine ⟨U0, fun U hU => ?_⟩
    refine le_trans (mul_le_mul ?_ le_rfl bot_le bot_le) (hU0 U hU)
    apply lintegral_mono_ae
    apply Filter.Eventually.of_forall
    intro u
    by_cases h : m * (1 - Real.cos (u * y)) ≤ K
    · rw [if_pos h, if_pos (le_trans h (le_max_left K 0))]
    · rw [if_neg h]
      by_cases h0 : m * (1 - Real.cos (u * y)) ≤ max K 0
      · rw [if_pos h0]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      · rw [if_neg h0]
