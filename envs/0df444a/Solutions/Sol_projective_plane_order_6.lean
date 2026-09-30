-- Prove2me | solution 1 for projective_plane_order_6
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:43:41.057703+00:00
-- url     : https://prove2.me/submissions/3eec893c-5934-4390-baca-9c0024d975c8

import Mathlib

open Finset

/-- `6` is not a sum of two rational squares (the prime `3 ≡ 3 (mod 4)` divides `6d²` to an
odd power). -/
theorem PP6_not_sum_two_sq (r s : ℚ) : r ^ 2 + s ^ 2 ≠ 6 := by
  intro h
  have hd : ((r.den : ℤ) * s.den) ≠ 0 := by positivity
  have hab : (r.num * s.den) ^ 2 + (s.num * r.den) ^ 2 = 6 * ((r.den : ℤ) * s.den) ^ 2 := by
    have h' : (r * (r.den * s.den)) ^ 2 + (s * (r.den * s.den)) ^ 2
        = 6 * ((r.den : ℚ) * s.den) ^ 2 := by
      rw [show (r * (r.den * s.den)) ^ 2 + (s * (r.den * s.den)) ^ 2
          = (r ^ 2 + s ^ 2) * ((r.den : ℚ) * s.den) ^ 2 by ring, h]
    have e1 : r * (r.den * s.den) = (r.num : ℚ) * s.den := by
      rw [← mul_assoc, Rat.mul_den_eq_num]
    have e2 : s * (r.den * s.den) = (s.num : ℚ) * r.den := by
      rw [mul_comm (r.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
    rw [e1, e2] at h'
    exact_mod_cast h'
  set a : ℤ := r.num * s.den
  set b : ℤ := s.num * r.den
  set d : ℤ := (r.den : ℤ) * s.den
  have hD : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  have hnat : 6 * d.natAbs ^ 2 = a.natAbs ^ 2 + b.natAbs ^ 2 := by
    have : ((6 * d.natAbs ^ 2 : ℕ) : ℤ) = ((a.natAbs ^ 2 + b.natAbs ^ 2 : ℕ) : ℤ) := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Int.natCast_natAbs,
        sq_abs]
      linarith
    exact_mod_cast this
  have hex : ∃ x y : ℕ, 6 * d.natAbs ^ 2 = x ^ 2 + y ^ 2 := ⟨_, _, hnat⟩
  rw [Nat.eq_sq_add_sq_iff] at hex
  have h3 : 3 ∈ (6 * d.natAbs ^ 2).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨by norm_num, ⟨2 * d.natAbs ^ 2, by ring⟩, by positivity⟩
  have hev := hex 3 h3 (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h36 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self]
    simp [padicValNat.eq_zero_of_not_dvd]
  rw [padicValNat.mul (by norm_num) (pow_ne_zero _ hD), padicValNat.pow, h36, Nat.even_iff] at hev
  omega

/-- `u ↦ Fin.cons (φ u) u` as a linear map. -/
def PP6_consL {n : ℕ} (φ : (Fin n → ℚ) →ₗ[ℚ] ℚ) : (Fin n → ℚ) →ₗ[ℚ] (Fin (n + 1) → ℚ) where
  toFun u := Fin.cons (φ u) u
  map_add' u u' := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp
  map_smul' a u := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp

theorem PP6_consL_zero {n : ℕ} (φ : (Fin n → ℚ) →ₗ[ℚ] ℚ) (u : Fin n → ℚ) : PP6_consL φ u 0 = φ u := by
  show (Fin.cons (φ u) u : Fin (n + 1) → ℚ) 0 = φ u
  exact Fin.cons_zero _ _

theorem PP6_consL_succ {n : ℕ} (φ : (Fin n → ℚ) →ₗ[ℚ] ℚ) (u : Fin n → ℚ) (j : Fin n) :
    PP6_consL φ u j.succ = u j := by
  show (Fin.cons (φ u) u : Fin (n + 1) → ℚ) j.succ = u j
  exact Fin.cons_succ _ _ _

/-- Sign-choice elimination: for `m` linear forms on `ℚ^(m+1)` there is a vector with last
coordinate `1` on which each form agrees up to sign with the corresponding coordinate. -/
theorem PP6_elim (m : ℕ) (L : Fin m → ((Fin (m + 1) → ℚ) →ₗ[ℚ] ℚ)) :
    ∃ v : Fin (m + 1) → ℚ, v (Fin.last m) = 1 ∧ ∀ i, (L i v) ^ 2 = (v i.castSucc) ^ 2 := by
  induction m with
  | zero => exact ⟨fun _ => 1, rfl, fun i => i.elim0⟩
  | succ m ih =>
    set c : ℚ := L 0 (Pi.single 0 1) with hc
    obtain ⟨ε, hε, hεc⟩ : ∃ ε : ℚ, ε ^ 2 = 1 ∧ ε - c ≠ 0 := by
      by_cases h : c = 1
      · exact ⟨-1, by norm_num, by rw [h]; norm_num⟩
      · exact ⟨1, by norm_num, sub_ne_zero.mpr (Ne.symm h)⟩
    let φ : (Fin (m + 1) → ℚ) →ₗ[ℚ] ℚ := (ε - c)⁻¹ • (L 0 ∘ₗ PP6_consL 0)
    have hdecomp : ∀ u : Fin (m + 1) → ℚ,
        PP6_consL φ u = (φ u) • Pi.single (0 : Fin (m + 2)) (1 : ℚ) + PP6_consL 0 u := by
      intro u
      ext i
      cases i using Fin.cases with
      | zero => simp [PP6_consL_zero]
      | succ j => simp [PP6_consL_succ]
    have key : ∀ u, L 0 (PP6_consL φ u) = ε * φ u := by
      intro u
      rw [hdecomp, map_add, map_smul, smul_eq_mul]
      have : L 0 (PP6_consL 0 u) = (ε - c) * φ u := by
        simp only [φ, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
        field_simp
      rw [this, ← hc]
      ring
    obtain ⟨u, hu1, hu⟩ := ih (fun i => L i.succ ∘ₗ PP6_consL φ)
    refine ⟨PP6_consL φ u, ?_, ?_⟩
    · rw [← Fin.succ_last, PP6_consL_succ]
      exact hu1
    · intro i
      cases i using Fin.cases with
      | zero => rw [key, mul_pow, hε, one_mul, Fin.castSucc_zero, PP6_consL_zero]
      | succ j =>
        have := hu j
        simp only [LinearMap.comp_apply] at this
        rw [this, ← Fin.succ_castSucc, PP6_consL_succ]

/-- Inverse of the quaternion-norm matrix for `6 = 2² + 1² + 1² + 0²`, i.e. `Bᵀ/6`. -/
def PP6_Binv : Fin 4 → Fin 4 → ℚ :=
  ![![2 / 6, 1 / 6, 1 / 6, 0], ![-1 / 6, 2 / 6, 0, -1 / 6],
    ![-1 / 6, 0, 2 / 6, 1 / 6], ![0, 1 / 6, -1 / 6, 2 / 6]]

def PP6_e : Fin 11 × Fin 4 ≃ Fin 44 := finProdFinEquiv

/-- The 44 linear forms `x_(q,r)(z) = ∑_{r'} PP6_Binv r r' z_(q,r')`. -/
def PP6_xf (qr : Fin 11 × Fin 4) : (Fin 44 → ℚ) →ₗ[ℚ] ℚ :=
  ∑ r', PP6_Binv qr.2 r' • LinearMap.proj (PP6_e (qr.1, r'))

theorem PP6_xf_apply (qr : Fin 11 × Fin 4) (z : Fin 44 → ℚ) :
    PP6_xf qr z = ∑ r', PP6_Binv qr.2 r' * z (PP6_e (qr.1, r')) := by
  simp [PP6_xf, LinearMap.sum_apply]

theorem PP6_foursq (z : Fin 44 → ℚ) :
    6 * ∑ qr : Fin 11 × Fin 4, (PP6_xf qr z) ^ 2 = ∑ k, (z k) ^ 2 := by
  have h : ∑ qr : Fin 11 × Fin 4, (z (PP6_e qr)) ^ 2 = ∑ k, (z k) ^ 2 :=
    Equiv.sum_comp PP6_e (fun k => (z k) ^ 2)
  rw [← h, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp only [PP6_xf_apply, Fin.sum_univ_four, PP6_Binv, Matrix.cons_val]
  ring

def PP6_x (j : Fin 44) : (Fin 44 → ℚ) →ₗ[ℚ] ℚ := PP6_xf (PP6_e.symm j)

theorem PP6_foursq' (z : Fin 44 → ℚ) : 6 * ∑ j, (PP6_x j z) ^ 2 = ∑ k, (z k) ^ 2 := by
  have h : ∑ j, (PP6_x j z) ^ 2 = ∑ qr, (PP6_xf qr z) ^ 2 :=
    Equiv.sum_comp PP6_e.symm (fun qr => (PP6_xf qr z) ^ 2)
  rw [h, PP6_foursq z]

/-- The quadratic identity from `N Nᵀ = 6 I + J`. -/
theorem PP6_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ι → ℚ)
    (hdiag : ∀ p, ∑ l, N p l * N p l = 7) (hoff : ∀ p q, p ≠ q → ∑ l, N p l * N q l = 1)
    (x : ι → ℚ) :
    ∑ l, (∑ p, N p l * x p) ^ 2 = 6 * ∑ p, (x p) ^ 2 + (∑ p, x p) ^ 2 := by
  have key : ∀ p q, ∑ l, N p l * N q l = 1 + if p = q then 6 else 0 := by
    intro p q
    split_ifs with h
    · subst h; rw [hdiag]; norm_num
    · rw [hoff p q h]; norm_num
  calc ∑ l, (∑ p, N p l * x p) ^ 2
      = ∑ l, ∑ p, ∑ q, (x p * x q) * (N p l * N q l) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by ring))
    _ = ∑ p, ∑ q, (x p * x q) * ∑ l, (N p l * N q l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun q _ => by rw [Finset.mul_sum])
    _ = ∑ p, ∑ q, (x p * x q + if p = q then 6 * (x p * x p) else 0) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        rw [key]
        split_ifs with h
        · subst h; ring
        · ring
    _ = ∑ p, ((∑ q, x p * x q) + 6 * (x p * x p)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = 6 * ∑ p, (x p) ^ 2 + (∑ p, x p) ^ 2 := by
        rw [Finset.sum_add_distrib, sq, Finset.sum_mul_sum, Finset.mul_sum]
        have : ∀ p, 6 * (x p * x p) = 6 * x p ^ 2 := fun p => by ring
        simp only [this]
        ring

theorem solution :
    ¬∃ (points lines : Finset (Fin 43)),
      points.card = 43 ∧ lines.card = 43 ∧
      ∃ (incident : Fin 43 → Fin 43 → Prop),
        (∀ i j : Fin 43, i ≠ j → ∃! l : Fin 43, incident i l ∧ incident j l) ∧
        (∀ l : Fin 43, {i : Fin 43 | incident i l}.ncard = 7) := by
  rintro ⟨points, lines, -, -, incident, h1, h2⟩
  classical
  -- the incidence matrix over ℚ
  let N : Fin 43 → Fin 43 → ℚ := fun p l => if incident p l then 1 else 0
  have hN01 : ∀ p l, N p l * N p l = N p l := by
    intro p l
    simp only [N]
    split_ifs <;> norm_num
  -- every line carries 7 points
  have hcol : ∀ l, ∑ p, N p l = 7 := by
    intro l
    have h := h2 l
    have hset : {i : Fin 43 | incident i l} = ↑(univ.filter (fun i => incident i l)) := by
      ext i; simp
    rw [hset, Set.ncard_coe_finset] at h
    simp only [N]
    rw [Finset.sum_boole]
    exact_mod_cast h
  -- two distinct points lie on exactly one common line
  have hoff : ∀ p q, p ≠ q → ∑ l, N p l * N q l = 1 := by
    intro p q hpq
    obtain ⟨l₀, hl₀, huniq⟩ := h1 p q hpq
    have hprod : ∀ l, N p l * N q l = if (incident p l ∧ incident q l) then 1 else 0 := by
      intro l
      simp only [N]
      by_cases hp : incident p l <;> by_cases hq : incident q l <;> simp [hp, hq]
    rw [Finset.sum_congr rfl (fun l _ => hprod l), Finset.sum_boole]
    rw [Nat.cast_eq_one, Finset.card_eq_one]
    refine ⟨l₀, ?_⟩
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => huniq l h, fun h => h ▸ hl₀⟩
  -- every point lies on 7 lines (double counting)
  have hrow : ∀ p, ∑ l, N p l = 7 := by
    intro p
    have h42 : ∑ q ∈ univ.erase p, ∑ l, N p l * N q l = 42 := by
      rw [Finset.sum_congr rfl (fun q hq => hoff p q (Finset.ne_of_mem_erase hq).symm)]
      simp [Finset.card_erase_of_mem]
    have hswap : ∑ q ∈ univ.erase p, ∑ l, N p l * N q l = ∑ l, N p l * (7 - N p l) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ p), hcol l]
    have h6 : ∑ l, N p l * (7 - N p l) = 6 * ∑ l, N p l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have := hN01 p l
      linear_combination -this
    linarith
  have hdiag : ∀ p, ∑ l, N p l * N p l = 7 := by
    intro p
    rw [Finset.sum_congr rfl (fun l _ => hN01 p l), hrow]
  -- the linear forms y_i(z) = ∑_p N p i x_p(z) on ℚ^44
  let y : Fin 43 → ((Fin 44 → ℚ) →ₗ[ℚ] ℚ) := fun i => ∑ p, N p i • PP6_x p.castSucc
  have hy : ∀ i z, y i z = ∑ p, N p i * PP6_x p.castSucc z := by
    intro i z
    simp [y, LinearMap.sum_apply]
  obtain ⟨v, hv1, hv⟩ := PP6_elim 43 y
  have hB := PP6_quad N hdiag hoff (fun p => PP6_x p.castSucc v)
  have e1 : ∑ i : Fin 43, (y i v) ^ 2 = ∑ i : Fin 43, (v i.castSucc) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => hv i)
  have e1' : ∑ i : Fin 43, (y i v) ^ 2 = ∑ l, (∑ p, N p l * PP6_x p.castSucc v) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [hy])
  have e2 := Fin.sum_univ_castSucc (fun k => (v k) ^ 2)
  have e3 := PP6_foursq' v
  have e4 := Fin.sum_univ_castSucc (fun j => (PP6_x j v) ^ 2)
  rw [hv1] at e2
  have h6 : 6 * (PP6_x (Fin.last 43) v) ^ 2 = 1 + (∑ p : Fin 43, PP6_x p.castSucc v) ^ 2 := by
    linarith
  set t := PP6_x (Fin.last 43) v with ht
  set w := ∑ p : Fin 43, PP6_x p.castSucc v with hw
  by_cases ht0 : t = 0
  · rw [ht0] at h6
    nlinarith [sq_nonneg w]
  · apply PP6_not_sum_two_sq (1 / t) (w / t)
    field_simp
    linarith
