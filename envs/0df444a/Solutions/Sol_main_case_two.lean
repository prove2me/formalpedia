-- Prove2me | solution 1 for main_case_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:51:08.048177+00:00
-- url     : https://prove2.me/submissions/e2122c98-fb57-42f8-8094-172a75568ed5

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Theorems.Thm_case_two_e1_even
import Theorems.Thm_case_two_d1_even_e1_odd
import Theorems.Thm_case_two_odd_small
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_isUnit_intCast_of_natAbs_coprime
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_zmod_set_swap
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


section
open Finset Pointwise
section Case2_MultipleCycles
variable {m : ℕ} {a b : ℤ}
local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁
private lemma intCast_2ba_eq :
    ((2 * b - a : ℤ) : ZMod m) = ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by grind
private lemma ZMod.val_add_one {n : ℕ} [NeZero n] (x : ZMod n) : (x + 1).val = (x.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
private lemma zmod_val_add_one (d : ℕ) [NeZero d] (i : ZMod d) :
    (i + 1).val = if i.val + 1 < d then i.val + 1 else 0 := by
  grind [ZMod.val_add_one, Nat.mod_eq_of_lt, Nat.mod_self]
section OrbitFramework
private lemma orbitMap_shift_b [NeZero m] (he1_b_zero : e₁ • (b : ZMod m) = 0) :
    ∀ p : ZMod d₁ × ZMod e₁, orbitMap m a b p + (b : ZMod m) = orbitMap m a b (p.1, p.2 + 1) := by
  intro ⟨i, j⟩
  simp only [orbitMap]
  by_cases hj : j.val + 1 < e₁
  · have hv : (j + 1).val = j.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hj
    rw [hv]
    grind
  · have hje : j.val + 1 = e₁ := by grind [ZMod.val_lt]
    have hv : (j + 1).val = 0 := by rw [ZMod.val_add_one, hje, Nat.mod_self]
    have h1 : (j.val : ZMod m) * ↑b + ↑b = 0 := by
      rw [← add_one_mul, ← Nat.cast_one, ← Nat.cast_add, hje, ← nsmul_eq_mul, he1_b_zero]
    rw [hv, Nat.cast_zero, zero_mul, add_zero, add_assoc, h1, add_zero]
private lemma orbitMap_shift_ba [NeZero m] (i : ZMod d₁) (j : ZMod e₁) (hi : i.val + 1 < d₁) :
    orbitMap m a b (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b (i + 1, j) := by
  simp only [orbitMap, zmod_val_add_one, if_pos hi]
  push_cast
  ring
private lemma orbitMap_cycle_index [NeZero m]
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁)) (i : ZMod d₁) (j : ZMod e₁) :
    ZMod.castHom d₁_dvd_m (ZMod d₁) (orbitMap m a b (i, j)) * u⁻¹ = i := by
  simp only [orbitMap, map_add, map_mul, map_natCast, map_intCast, b_zero_mod_d1, mul_zero,
    add_zero, mul_assoc, ← hu, Units.mul_inv, mul_one]
  simp [ZMod.natCast_val]
private lemma cycle_index_shift_ba [NeZero m]
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁)) (x : ZMod m) :
    ZMod.castHom d₁_dvd_m (ZMod d₁) (x + ↑(b - a)) * u⁻¹ =
    ZMod.castHom d₁_dvd_m (ZMod d₁) x * u⁻¹ + 1 := by
  simp only [map_add, map_intCast, add_mul, ← hu, Units.mul_inv]
private lemma equiv_symm_shift_b {γ : Type*} [AddCommMonoid γ]
    (Φ : ZMod d₁ × ZMod e₁ ≃ γ) {b : γ}
    (hΦ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, Φ (i, j + 1) = Φ (i, j) + b) (x : γ) :
    Φ.symm (x + b) = ((Φ.symm x).1, (Φ.symm x).2 + 1) := by grind
private lemma equiv_symm_fst_eq {γ : Type*} (Φ : ZMod d₁ × ZMod e₁ ≃ γ) (α : γ → ZMod d₁)
    (hα : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (Φ (i, j)) = i) (x : γ) :
    (Φ.symm x).1 = α x := by grind
private lemma orbitEquiv_shift_b [NeZero m] {h_gcd_coprime : Nat.gcd d₁ d₂ = 1} (x : ZMod m) :
    (orbitEquiv h_gcd_coprime).symm (x + ↑b) =
    (((orbitEquiv h_gcd_coprime).symm x).1, ((orbitEquiv h_gcd_coprime).symm x).2 + 1) :=
  equiv_symm_shift_b _ (fun i j =>
    (orbitMap_shift_b (addOrderOf_b_eq (b := b) (m := m) ▸
      addOrderOf_nsmul_eq_zero _) (i, j)).symm) x
private lemma orbitEquiv_cycle_shift [NeZero m] {h_gcd_coprime : Nat.gcd d₁ d₂ = 1} (x : ZMod m) :
    ((orbitEquiv h_gcd_coprime).symm (x + ↑(b - a))).1 =
    ((orbitEquiv h_gcd_coprime).symm x).1 + 1 := by
  have hba_unit := isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)
  let u_ba := hba_unit.choose
  have hu_ba : ↑u_ba = ((b - a : ℤ) : ZMod d₁) := hba_unit.choose_spec
  let α : ZMod m → ZMod d₁ := fun x => ZMod.castHom d₁_dvd_m (ZMod d₁) x * u_ba⁻¹
  have hΦ_cycle := equiv_symm_fst_eq (orbitEquiv h_gcd_coprime) α (orbitMap_cycle_index u_ba hu_ba)
  rw [hΦ_cycle (x + ↑(b - a))]
  dsimp only [α]
  rw [cycle_index_shift_ba u_ba hu_ba]
  grind
private lemma orbitEquiv_snd_shift_ba [NeZero m] {h_gcd_coprime : Nat.gcd d₁ d₂ = 1}
    (n : ZMod m) (hi : (orbitEquiv h_gcd_coprime).symm n |>.1.val + 1 < d₁) :
    ((orbitEquiv h_gcd_coprime).symm (n + ↑(b - a))).2 = ((orbitEquiv h_gcd_coprime).symm n).2 := by
  set Φ := orbitEquiv h_gcd_coprime
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  have hshift := orbitMap_shift_ba (a := a) i j hi
  have hn : Φ (i, j) = n := Prod.eta (Φ.symm n) ▸ Equiv.apply_symm_apply Φ n
  have hΦ : Φ (i + 1, j) = n + ↑(b - a) := by
    simp only [Φ, orbitEquiv, Equiv.ofBijective_apply] at hn ⊢
    grind
  rw [← hΦ, Φ.symm_apply_apply]
private lemma orbit_coloring_polychrom (Φ : ZMod d₁ × ZMod e₁ ≃ ZMod m)
    (hΦ_add_b : ∀ x : ZMod m, Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1))
    (hΦ_cycle_shift : ∀ x : ZMod m, (Φ.symm (x + ↑(b - a))).1 = (Φ.symm x).1 + 1)
    (f : ZMod d₁ × ZMod e₁ → Fin 3) (hcovers : ∀ (n : ZMod m) (k : Fin 3),
      k = f ((Φ.symm n).1, (Φ.symm n).2) ∨
      k = f ((Φ.symm n).1, (Φ.symm n).2 + 1) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2 + 1)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  let χ : ZMod m → Fin 3 := f ∘ Φ.symm
  refine ⟨χ, fun n k => ?_⟩
  simp only [zmod_set, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  set j' := (Φ.symm (n + ↑(b - a))).2
  have hχ_n : χ n = f (i, j) := rfl
  have hχ_nb : χ (n + ↑b) = f (i, j + 1) := congr_arg f (hΦ_add_b n)
  have hχ_nba : χ (n + ↑(b - a)) = f (i + 1, j') := congr_arg f (Prod.ext (hΦ_cycle_shift n) rfl)
  have hχ_n2ba : χ (n + ↑(2 * b - a)) = f (i + 1, j' + 1) := by
    have : (n : ZMod m) + ↑(2 * b - a) = (n + ↑(b - a)) + ↑b := by rw [intCast_2ba_eq, add_assoc]
    grind
  rcases hcovers n k with h | h | h | h
  · exact ⟨0, by simp, by rw [add_zero, hχ_n, h]⟩
  all_goals grind
private lemma case2d_uv_le {e : ℕ} (hge : e ≥ 19) : case2d_u e + case2d_v e ≤ e := by
  grind [case2d_u, case2d_v]
private lemma basePattern_consec_pair {e j : ℕ} (he : Odd e) (hge : e ≥ 19) (hj : j < e) :
    intervalColors (whichInterval e j) ⊆ {basePattern e j, basePattern e ((j + 1) % e)} := by
  obtain ⟨ku, hku⟩ : Odd (case2d_u e) := by obtain ⟨k, hk⟩ := he; grind [case2d_u]
  obtain ⟨kv, hkv⟩ : Odd (case2d_v e) := by obtain ⟨k, hk⟩ := he; grind [case2d_v]
  obtain ⟨kw, hkw⟩ : Odd (e - case2d_u e - case2d_v e) := by
    obtain ⟨k, hk⟩ := he; grind [case2d_u, case2d_v]
  have huv := case2d_uv_le hge
  by_cases hj1 : j + 1 < e
  · rw [Nat.mod_eq_of_lt hj1]
    by_cases hsame : whichInterval e j = whichInterval e (j + 1)
    · -- Same interval: both colors present
      have : {basePattern e j, basePattern e (j + 1)} = intervalColors (whichInterval e j) := by
        simp only [whichInterval, basePattern, intervalColors] at *
        grind
      exact this.ge
    · -- Boundary: last element of interval + first of next
      simp only [whichInterval] at hsame ⊢
      grind [basePattern, intervalColors]
  · -- Wrap: j = e - 1
    push Not at hj1
    have hj_eq : j = e - 1 := by grind
    subst hj_eq
    have : e - 1 + 1 = e := by grind
    rw [this, Nat.mod_self]
    simp only [whichInterval]
    grind [basePattern, intervalColors]
private lemma rotation_changes_interval {e j : ℕ} (hge : e ≥ 19) (hj : j < e)
    {r : ℕ} (hr_lo : case2d_u e ≤ r) (hr_hi : r ≤ e - case2d_u e) :
    whichInterval e j ≠ whichInterval e ((j + r) % e) := by
  have he_pos : 0 < e := by grind
  have huv_bound := case2d_uv_le hge
  have hv_le_u : case2d_v e ≤ case2d_u e := by grind [case2d_u, case2d_v]
  have hw_le_u : e - (case2d_u e + case2d_v e) ≤ case2d_u e := by grind [case2d_u, case2d_v]
  simp only [whichInterval]
  have hj'_lt : (j + r) % e < e := Nat.mod_lt _ he_pos
  intro heq
  by_cases hjr_wrap : j + r < e
  · -- No wrap
    rw [Nat.mod_eq_of_lt hjr_wrap] at heq hj'_lt
    grind
  · -- Wrap: (j + r) % e = j + r - e
    push Not at hjr_wrap
    have hmod : (j + r) % e = j + r - e := by
      have : r < e := by grind
      have h1 : j + r - e < e := by grind
      rw [Nat.add_mod_eq_sub, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt this, if_neg (by grind)]
    grind
private lemma basePattern_rotation_covers {e j : ℕ} (he : Odd e) (hge : e ≥ 19)
    {r : ℕ} (hr_lo : case2d_u e ≤ r) (hr_hi : r ≤ e - case2d_u e) (hj : j < e) :
    ∀ k : Fin 3, k ∈ ({basePattern e j, basePattern e ((j + 1) % e),
        basePattern e ((j + r) % e), basePattern e ((j + r + 1) % e)} : Finset (Fin 3)) := by
  intro k
  have he_pos : 0 < e := by grind
  have hI := rotation_changes_interval hge hj hr_lo hr_hi
  have h1 := basePattern_consec_pair he hge hj
  have hjr : (j + r) % e < e := Nat.mod_lt _ he_pos
  have h2 := basePattern_consec_pair he hge hjr
  -- Rewrite ((j + r) % e + 1) % e = (j + r + 1) % e
  have hmod : ((j + r) % e + 1) % e = (j + r + 1) % e := Nat.mod_add_mod (j + r) e 1
  rw [hmod] at h2
  have : ∀ (i₁ i₂ : Fin 3), i₁ ≠ i₂ → k ∈ intervalColors i₁ ∨ k ∈ intervalColors i₂ := by
    intro i₁ i₂
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases k <;>
      simp_all [intervalColors, Finset.mem_insert, Finset.mem_singleton]
  grind
private lemma case2d_wrap_shift [NeZero m] (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) :
    ∃ k₀ : ZMod e₁, (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m) := by
  set Φ := orbitEquiv h_gcd_coprime
  set q := Φ.symm ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  have hq_i : q.1 = 0 := by
    set f := ZMod.castHom d₁_dvd_m (ZMod d₁)
    have hfφ : f (Φ q) = q.1 * ((b - a : ℤ) : ZMod d₁) := by
      change f (orbitMap m a b q) = _
      simp only [orbitMap, map_add, map_mul, map_natCast, map_intCast,
        b_zero_mod_d1, mul_zero, add_zero]
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [Equiv.apply_symm_apply] at hfφ
    have : f (d₁ • ((b - a : ℤ) : ZMod m)) = 0 := by
      rw [nsmul_eq_mul, map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]
    rw [this] at hfφ
    exact (isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)).mul_left_eq_zero.mp
      hfφ.symm
  refine ⟨q.2, ?_⟩
  have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  change orbitMap m a b q = _ at hφq
  simp only [orbitMap] at hφq
  rw [(Prod.eta q).symm] at hφq
  simp only [hq_i, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add] at hφq
  grind
private lemma case2d_shift_ba_wrap [NeZero m] (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁) (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (i : ZMod d₁) (hi : i.val = d₁ - 1) : ∀ (j : ZMod e₁),
    orbitMap m a b (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b ((0 : ZMod d₁), j + k₀) := by
  intro j
  simp only [orbitMap, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add]
  have hpred : (d₁ - 1 + 1 : ℕ) = d₁ := Nat.succ_pred (NeZero.ne d₁)
  -- Step 1: rearrange i.val*(b-a) + j*b + (b-a) = d₁*(b-a) + j*b
  have hcast : (↑i.val : ZMod m) + 1 = (↑d₁ : ZMod m) := by
    rw [hi, ← Nat.cast_one (R := ZMod m), ← Nat.cast_add, hpred]
  have step1 : (↑i.val : ZMod m) * ((b - a : ℤ) : ZMod m) +
      ↑↑j.val * ((b : ℤ) : ZMod m) + ((b - a : ℤ) : ZMod m) =
      (↑d₁ : ZMod m) * ((b - a : ℤ) : ZMod m) + ↑↑j.val * ((b : ℤ) : ZMod m) := by grind
  rw [step1, ← nsmul_eq_mul (d₁), hk₀, nsmul_eq_mul, ← add_mul,
    ← Nat.cast_add (k₀.val) (j.val), ← nsmul_eq_mul, Nat.add_comm]
  -- Reduce (j+k₀) • b mod e₁ using he1_b_zero
  set n := j.val + k₀.val
  have h1 : (j + k₀).val = n % e₁ := ZMod.val_add j k₀
  rw [h1]
  conv_lhs => rw [(Nat.div_add_mod n e₁).symm]
  rw [add_nsmul, mul_nsmul, he1_b_zero, smul_zero, zero_add, nsmul_eq_mul]
private lemma orbitEquiv_snd_shift_ba_wrap [NeZero m]
    {h_gcd_coprime : Nat.gcd d₁ d₂ = 1} (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁) (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (n : ZMod m) (hi : (orbitEquiv h_gcd_coprime).symm n |>.1.val = d₁ - 1) :
    ((orbitEquiv h_gcd_coprime).symm (n + ↑(b - a))).2 =
    ((orbitEquiv h_gcd_coprime).symm n).2 + k₀ := by
  set Φ := orbitEquiv h_gcd_coprime
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  have hshift := case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi
  have hn : Φ (i, j) = n := Prod.eta (Φ.symm n) ▸ Equiv.apply_symm_apply Φ n
  have hΦ : Φ ((0 : ZMod d₁), j + k₀) = n + ↑(b - a) := by
    simp only [Φ, orbitEquiv, Equiv.ofBijective_apply] at hn ⊢
    grind
  grind
private lemma case2d_rotation_sum_exists {e d : ℕ} [NeZero d]
    (hd_ge : d ≥ 5) (he_ge : e ≥ 19) (he_odd : Odd e) (target : ℕ) :
    ∃ vals : ZMod d → ℕ,
      (∀ i, case2d_u e ≤ vals i ∧ vals i ≤ e - case2d_u e) ∧
      (Finset.univ.sum vals) % e = target % e := by
  have hu_lt : case2d_u e < e := by grind [case2d_u]
  have hdw' : d * (e - 2 * case2d_u e) ≥ e := by
    change d * (e - 2 * (e / 3 + e % 3)) ≥ e
    obtain ⟨k, hk⟩ := he_odd
    subst hk
    have h5w : 5 * ((2 * k + 1) - 2 * ((2 * k + 1) / 3 + (2 * k + 1) % 3)) ≥ 2 * k + 1 := by grind
    exact le_trans h5w (by gcongr)
  set u := case2d_u e
  set w := e - 2 * u
  have hw_pos : 0 < w := by grind
  set deficit := (target + e * d - d * u) % e
  have hdef_lt : deficit < e := Nat.mod_lt _ (by grind)
  set q := deficit / w
  set r := deficit % w
  have hr_lt : r < w := Nat.mod_lt _ hw_pos
  have hq_lt : q < d := by
    by_contra! hge
    have h1 : deficit ≥ d * w :=
      calc deficit ≥ deficit / w * w := Nat.div_mul_le_self deficit w
        _ = q * w := rfl
        _ ≥ d * w := by gcongr
    grind
  have hqr : w * q + r = deficit := Nat.div_add_mod deficit w
  let f : ZMod d → ℕ := fun i => if i.val < q then e - u else if i.val = q then u + r else u
  refine ⟨f, fun i => ?_, ?_⟩
  · grind
  · let g : ZMod d → ℕ := fun i =>
      if i.val < q then w else if i.val = q then r else 0
    have hfg : ∀ i : ZMod d, f i = u + g i := by grind
    have hsum_f : Finset.univ.sum f = d * u + Finset.univ.sum g := by
      conv_lhs => arg 2; ext i; rw [hfg i]
      simp [Finset.sum_add_distrib, Finset.card_univ, ZMod.card]
    have hcard_lt : (Finset.univ.filter (fun i : ZMod d => i.val < q)).card = q := by
      have : Finset.image ZMod.val (Finset.univ.filter (fun i : ZMod d => i.val < q)) =
          Finset.range q := by
        ext j
        simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
        exact ⟨fun ⟨_, hx, he⟩ => he ▸ hx, fun hj => ⟨(j : ZMod d),
          by rwa [ZMod.val_natCast_of_lt (lt_trans hj hq_lt)],
          ZMod.val_natCast_of_lt (lt_trans hj hq_lt)⟩⟩
      rw [← Finset.card_image_of_injective _ (ZMod.val_injective _), this, Finset.card_range]
    have hcard_eq : (Finset.univ.filter (fun i : ZMod d => i.val = q)).card = 1 := by
      have : Finset.univ.filter (fun i : ZMod d => i.val = q) = {(q : ZMod d)} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => ZMod.val_injective _ (by rwa [ZMod.val_natCast_of_lt hq_lt]),
          fun h => by rw [h, ZMod.val_natCast_of_lt hq_lt]⟩
      rw [this, Finset.card_singleton]
    have hsum_g : Finset.univ.sum g = q * w + r := by
      have : ∀ i : ZMod d,
          g i = (if i.val < q then w else 0) + (if i.val = q then r else 0) := by grind
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        smul_eq_mul, hcard_lt, hcard_eq, one_mul]
    rw [hsum_f, hsum_g, Nat.mul_comm q w, hqr]
    simp only [deficit]
    rw [Nat.add_mod_mod, Nat.add_sub_cancel' (le_add_left (le_trans
      (Nat.mul_le_mul_left d (le_of_lt hu_lt)) (by rw [Nat.mul_comm]))),
      Nat.add_mul_mod_self_left]
private lemma zmod_filter_sum_succ {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n) :
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val + 1)).sum f =
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i := by
  have hsplit : Finset.univ.filter (fun k : ZMod n => k.val < i.val + 1) =
      Finset.univ.filter (fun k : ZMod n => k.val < i.val) ∪ {i} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton]
    grind [ZMod.val_injective]
  grind
private lemma zmod_filter_sum_last {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n)
    (hi : i.val = n - 1) : (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i =
    Finset.univ.sum f := by rw [← zmod_filter_sum_succ f i]; congr 1; grind
private lemma pos_shift_one {n : ℕ} [NeZero n] (j : ZMod n) (c : ℕ) :
    ((j + 1).val + c) % n = ((j.val + c) % n + 1) % n := by
  rw [ZMod.val_add_one, Nat.mod_add_mod, Nat.mod_add_mod]
  grind
private lemma pos_shift_succ' (j S V n : ℕ) :
    (j + (S + V) % n) % n = ((j + S % n) % n + V) % n := by
  have h1 : j + (S + V) = j + S + V := (Nat.add_assoc j S V).symm
  rw [Nat.add_mod_mod, h1, ← Nat.mod_add_mod (j + S) n V, (Nat.add_mod_mod j S n).symm]
private lemma pos_shift_wrap' (j S V k₀ n : ℕ) (hsum : (S + V) % n = k₀ % n) :
    (j + k₀) % n = ((j + S % n) % n + V) % n := by
  rw [← Nat.add_mod_mod j k₀ n, ← hsum, pos_shift_succ']
private lemma case2d_coloring_works (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (hd1_odd : Odd d₁) (he1_odd : Odd e₁)
    (he1_ge : e₁ ≥ 19) (h3 : ¬ (3 ∣ d₁)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  haveI : NeZero m := ⟨by omega⟩
  have he1_b_zero : e₁ • (b : ZMod m) = 0 :=
    addOrderOf_b_eq (b := b) (m := m) ▸ addOrderOf_nsmul_eq_zero _
  let Φ := orbitEquiv h_gcd_coprime
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift h_gcd_coprime
  have hd1_ge5 : d₁ ≥ 5 := by grind
  obtain ⟨vals, hvals_bound, hvals_sum⟩ := case2d_rotation_sum_exists hd1_ge5 he1_ge he1_odd k₀.val
  let rot : ZMod d₁ → ℕ := fun i =>
    ((Finset.univ.filter (fun j : ZMod d₁ => j.val < i.val)).sum vals) % e₁
  let f : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
    basePattern e₁ ((j.val + rot i) % e₁)
  exact orbit_coloring_polychrom Φ orbitEquiv_shift_b orbitEquiv_cycle_shift f (fun n k => by
    set i := (Φ.symm n).1
    set j := (Φ.symm n).2
    set j' := (Φ.symm (n + ↑(b - a))).2
    set p := (j.val + rot i) % e₁ with hp_def
    have hp_lt : p < e₁ := Nat.mod_lt _ (NeZero.pos e₁)
    have covers := basePattern_rotation_covers he1_odd he1_ge
      (hvals_bound i).1 (hvals_bound i).2 hp_lt k
    simp only [Finset.mem_insert, Finset.mem_singleton] at covers
    suffices hpos : (j'.val + rot (i + 1)) % e₁ = (p + vals i) % e₁ by
      rcases covers with h | h | h | h
      · left; exact h
      · right; left; rw [h]; simp only [f]; congr 1; exact (pos_shift_one j (rot i)).symm
      · right; right; left; rw [h]; simp only [f]; grind
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [h]
        simp only [f]
        congr 1
        calc (p + vals i + 1) % e₁
            = ((p + vals i) % e₁ + 1) % e₁ := (Nat.mod_add_mod (p + vals i) e₁ 1).symm
          _ = ((j'.val + rot (i + 1)) % e₁ + 1) % e₁ := by rw [hpos]
          _ = ((j' + 1 : ZMod e₁).val + rot (i + 1)) % e₁ :=
              (pos_shift_one j' (rot (i + 1))).symm
    by_cases hi : i.val + 1 < d₁
    · have hj'_eq : j' = j := orbitEquiv_snd_shift_ba n hi
      rw [hj'_eq]
      change (j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < (i + 1).val)).sum vals) % e₁) % e₁ =
        ((j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < i.val)).sum vals) % e₁) % e₁ + vals i) % e₁
      have : (i + 1).val = i.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
      rw [this, zmod_filter_sum_succ vals i]
      exact pos_shift_succ' j.val _ (vals i) e₁
    · have hi_eq : i.val = d₁ - 1 := by grind [ZMod.val_lt]
      have hj'_eq : j' = j + k₀ :=
        orbitEquiv_snd_shift_ba_wrap he1_b_zero k₀ hk₀ n hi_eq
      rw [hj'_eq]
      have hi1_zero : (i + 1 : ZMod d₁) = 0 :=
        ZMod.val_injective _ (by rw [ZMod.val_add_one, hi_eq, ZMod.val_zero]; grind [Nat.mod_self])
      have hrot0 : rot (0 : ZMod d₁) = 0 := by simp [rot, ZMod.val_zero]
      rw [hi1_zero, hrot0, Nat.add_zero, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl e₁)]
      exact pos_shift_wrap' j.val _ (vals i) k₀.val e₁
        (by rw [zmod_filter_sum_last vals i hi_eq, hvals_sum]))
private lemma no_both_e_small {m' d d' : ℕ} (hm : m' ≥ 289) (hcop : Nat.gcd d d' = 1)
    (hd_gt1 : d > 1) (hd'_gt1 : d' > 1) (hd_dvd : d ∣ m') (hd'_dvd : d' ∣ m')
    (he_le : m' / d ≤ 17) (he'_le : m' / d' ≤ 17) : False := by
  have hprod := Nat.le_of_dvd (by grind)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by rwa [Nat.Coprime]) hd_dvd hd'_dvd)
  have h₁ : m' ≤ d * 17 := by rw [← Nat.mul_div_cancel' hd_dvd]; gcongr
  have h₂ : m' ≤ d' * 17 := by rw [← Nat.mul_div_cancel' hd'_dvd]; gcongr
  have := Nat.le_of_mul_le_mul_left (hprod.trans h₁) (by grind)
  have := Nat.le_of_mul_le_mul_left (mul_comm d d' ▸ hprod.trans h₂) (by grind)
  -- 289 ≤ m ≤ d₁*17 → d₁ ≥ 17; similarly d₂ ≥ 17
  -- So d₁ = d₂ = 17, gcd(17,17) = 17 ≠ 1.
  grind
end OrbitFramework
end Case2_MultipleCycles
end

set_option autoImplicit true
open Finset Pointwise
variable {m : ℕ} {a b : ℤ}
local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁
theorem _root_.solution (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) (h_min : min d₁ d₂ > 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  rcases Nat.even_or_odd e₁ with he | ho
  · exact case_two_e1_even hm h_gcd_coprime h_min he
  · rcases Nat.even_or_odd d₁ with hd | hd
    · exact case_two_d1_even_e1_odd hm h_gcd_coprime h_min hd ho
    · -- Both d₁ and e₁ odd.
      -- Paper: "Choose the smallest of d₁,d₂ not a multiple of 3, WLOG d₁."
      -- Swap if 3 ∣ d₁, then dispatch with 3 ∤ d₁.
      suffices dispatch : ∀ (a' b' : ℤ),
          (Nat.gcd b'.natAbs m).gcd (Nat.gcd (b' - a').natAbs m) = 1 →
          min (Nat.gcd b'.natAbs m) (Nat.gcd (b' - a').natAbs m) > 1 →
          Odd (Nat.gcd b'.natAbs m) →
          Odd (m / Nat.gcd b'.natAbs m) →
          ¬ (3 ∣ Nat.gcd b'.natAbs m) →
          HasPolychromColouring (Fin 3) (zmod_set m a' b') by
        by_cases h3 : 3 ∣ d₁
        · -- Swap roles of b and b-a
          rw [← zmod_set_swap m a b]
          set a' := (-a : ℤ)
          set b' := (b - a : ℤ)
          have hba_eq : (b' - a').natAbs = b.natAbs := by grind
          have hcop' : (Nat.gcd b'.natAbs m).gcd (Nat.gcd (b' - a').natAbs m) = 1 := by grind
          have hmin' : min (Nat.gcd b'.natAbs m) (Nat.gcd (b' - a').natAbs m) > 1 := by grind
          have h3' : ¬ (3 ∣ Nat.gcd b'.natAbs m) := by
            intro h3d'
            have := Nat.dvd_gcd h3 h3d'
            grind
          rcases Nat.even_or_odd (m / Nat.gcd b'.natAbs m) with he' | ho'
          · exact case_two_e1_even hm hcop' hmin' he'
          · rcases Nat.even_or_odd (Nat.gcd b'.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd hm hcop' hmin' hd' ho'
            · exact dispatch a' b' hcop' hmin' hd' ho' h3'
        · exact dispatch a b h_gcd_coprime h_min hd ho h3
      -- Prove dispatch: given ¬(3 ∣ d₁), split on e₁ size
      intro a' b' hcop hmin hd₁_odd he₁_odd h3_nd₁
      set d := Nat.gcd b'.natAbs m
      set d₂' := Nat.gcd (b' - a').natAbs m
      set e := m / d
      have hd_dvd : d ∣ m := Nat.gcd_dvd_right _ _
      have hd₂_dvd : d₂' ∣ m := Nat.gcd_dvd_right _ _
      by_cases he_le : e ≤ 17
      · -- Case 2c: prove 3 ∣ e
        -- Since gcd(d,d₂')=1 and 3 ∤ d, if 3 ∣ d₂' then 3 ∣ m hence 3 ∣ e.
        -- If 3 ∤ d₂': swap and show e₂ ≥ 19 (contradiction with both ≤ 17).
        by_cases h3d₂ : 3 ∣ d₂'
        · have h3m : 3 ∣ m := dvd_trans h3d₂ hd₂_dvd
          have h3e : 3 ∣ e :=
            ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h3_nd₁).dvd_of_dvd_mul_left
              (Nat.mul_div_cancel' hd_dvd ▸ h3m)
          exact case_two_odd_small hm hcop hmin hd₁_odd h3e
        · -- 3 ∤ d and 3 ∤ d₂ and e ≤ 17: swap and show new e ≥ 19.
          -- After swap, new e₁' = m/d₂. If e₁' ≤ 17 too, contradiction.
          rw [← zmod_set_swap m a' b']
          set a'' := (-a' : ℤ)
          set b'' := (b' - a' : ℤ)
          have hba_eq : (b'' - a'').natAbs = b'.natAbs := by grind
          have hcop' : (Nat.gcd b''.natAbs m).gcd (Nat.gcd (b'' - a'').natAbs m) = 1 := by grind
          have hmin' : min (Nat.gcd b''.natAbs m) (Nat.gcd (b'' - a'').natAbs m) > 1 := by grind
          -- Dispatch on parity
          rcases Nat.even_or_odd (m / Nat.gcd b''.natAbs m) with he' | ho'
          · exact case_two_e1_even hm hcop' hmin' he'
          · rcases Nat.even_or_odd (Nat.gcd b''.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd hm hcop' hmin' hd' ho'
            · -- Both odd after swap. Show e₁' ≥ 19 by contradiction.
              have he₁'_ge : m / Nat.gcd b''.natAbs m ≥ 19 := by
                by_contra! hlt
                rw [Nat.gcd_comm] at hcop
                exact no_both_e_small hm hcop (by grind) (by grind) hd₂_dvd hd_dvd (by grind) he_le
              exact case2d_coloring_works hm hcop' hmin' hd' ho' he₁'_ge h3d₂
      · have he_ge : e ≥ 19 := by grind
        exact case2d_coloring_works hm hcop hmin hd₁_odd he₁_odd he_ge h3_nd₁
