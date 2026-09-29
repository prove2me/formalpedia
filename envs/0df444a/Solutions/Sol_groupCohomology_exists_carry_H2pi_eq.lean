-- Prove2me | solution 1 for groupCohomology.exists_carry_H2pi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c383f7cd-c7fc-581c-a163-d62515597f61

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_carry_H2pi_eq

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_carry_H2pi_eq.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2π congr cocycles₂ d₁₂_hom_apply coboundaries₂ map mem_cocycles₂_iff δ H2π_eq_zero_iff cyclicLog carryFun cyclicInv carryFun_mem_cocycles2"
p2m_open "groupCohomology"
section
variable {G : Type} [Group G]

namespace Ws26HL2

theorem pow_cyclicLog (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g : G) :
    s ^ cyclicLog s hs hfin g = g := by
  unfold cyclicLog
  have := (finEquivZPowers hfin).apply_symm_apply ⟨g, hs g⟩
  rw [finEquivZPowers_apply] at this
  exact congrArg Subtype.val this

theorem cyclicLog_lt (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g : G) :
    cyclicLog s hs hfin g < orderOf s :=
  ((finEquivZPowers hfin).symm ⟨g, hs g⟩).isLt

theorem cyclicLog_eq_of_pow_eq (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {i : ℕ} (hi : i < orderOf s) {g : G} (h : s ^ i = g) : cyclicLog s hs hfin g = i := by
  apply pow_injOn_Iio_orderOf (x := s)
  · exact cyclicLog_lt s hs hfin g
  · exact hi
  · show s ^ cyclicLog s hs hfin g = s ^ i
    rw [pow_cyclicLog, h]

theorem cyclicLog_mul (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g h : G) :
    (cyclicLog s hs hfin (g * h) : ℤ) = cyclicLog s hs hfin g + cyclicLog s hs hfin h
      - if orderOf s ≤ cyclicLog s hs hfin g + cyclicLog s hs hfin h then (orderOf s : ℤ) else 0 := by
  set n := orderOf s with hn
  set i := cyclicLog s hs hfin g
  set k := cyclicLog s hs hfin h
  have hi : i < n := cyclicLog_lt s hs hfin g
  have hk : k < n := cyclicLog_lt s hs hfin h
  have hgh : s ^ (i + k) = g * h := by rw [pow_add, pow_cyclicLog, pow_cyclicLog]
  split_ifs with hle
  · have h1 : cyclicLog s hs hfin (g * h) = i + k - n := by
      apply cyclicLog_eq_of_pow_eq s hs hfin (by omega)
      rw [← hgh]
      conv_rhs => rw [show i + k = (i + k - n) + n by omega, pow_add, pow_orderOf_eq_one, mul_one]
    rw [h1]; push_cast [Nat.cast_sub hle]; ring
  · have h1 : cyclicLog s hs hfin (g * h) = i + k := cyclicLog_eq_of_pow_eq s hs hfin (by omega) hgh
    rw [h1]; push_cast; ring

theorem rho_eq_self_of_generator (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) {A : Rep ℤ G} {a : A}
    (ha : A.ρ s a = a) (g : G) : A.ρ g a = a := by
  obtain ⟨m, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hs g)
  have hpow : ∀ k : ℕ, A.ρ (s ^ k) a = a := by
    intro k
    induction k with
    | zero => rw [pow_zero, MonoidHom.map_one]; rfl
    | succ k ih =>
      rw [pow_succ, MonoidHom.map_mul]
      show A.ρ (s ^ k) (A.ρ s a) = a
      rw [ha, ih]
  cases m with
  | ofNat k => show A.ρ (s ^ (k : ℤ)) a = a; rw [zpow_natCast]; exact hpow k
  | negSucc k =>
    rw [zpow_negSucc]
    have h1 := hpow (k + 1)
    have : A.ρ (s ^ (k + 1))⁻¹ (A.ρ (s ^ (k + 1)) a) = a := by
      rw [show A.ρ (s ^ (k + 1))⁻¹ (A.ρ (s ^ (k + 1)) a) = (A.ρ (s ^ (k + 1))⁻¹ * A.ρ (s ^ (k + 1))) a from rfl,
        ← MonoidHom.map_mul, inv_mul_cancel, MonoidHom.map_one]; rfl
    rw [h1] at this
    exact this

theorem carryFun_apply (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (a : A) (g h : G) :
    carryFun s hs hfin a (g, h) = (if orderOf s ≤ cyclicLog s hs hfin g + cyclicLog s hs hfin h then (1 : ℤ) else 0) • a := by
  unfold carryFun
  split_ifs <;> simp

end Ws26HL2

namespace Ws26HL2

variable {G : Type} [Group G]

noncomputable def psum (s : G) {A : Rep ℤ G} (c : G × G → A) (m : ℕ) : A :=
  ∑ k ∈ Finset.range m, c (s ^ k, s)

theorem psum_zero (s : G) {A : Rep ℤ G} (c : G × G → A) : psum s c 0 = 0 := by
  simp [psum]

theorem psum_succ (s : G) {A : Rep ℤ G} (c : G × G → A) (m : ℕ) :
    psum s c (m + 1) = psum s c m + c (s ^ m, s) := by
  simp [psum, Finset.sum_range_succ]

theorem psum_add (s : G) {A : Rep ℤ G} (c : G × G → A) (i j : ℕ) :
    psum s c (i + j) = psum s c i + ∑ k ∈ Finset.range j, c (s ^ (i + k), s) := by
  simp only [psum, Finset.sum_range_add]

theorem psum_orderOf_add (s : G) {A : Rep ℤ G} (c : G × G → A) (r : ℕ) :
    psum s c (orderOf s + r) = psum s c (orderOf s) + psum s c r := by
  rw [psum_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add, pow_orderOf_eq_one, one_mul]

theorem cyclicInv_eq_psum (s : G) {A : Rep ℤ G} (c : G × G → A) : cyclicInv s c = psum s c (orderOf s) := rfl

theorem cocycle_id {A : Rep ℤ G} (c : cocycles₂ A) (g h j : G) :
    c (g * h, j) + c (g, h) = A.ρ g (c (h, j)) + c (g, h * j) :=
  (mem_cocycles₂_iff (A := A) c).mp c.2 g h j

theorem cocycle_one {A : Rep ℤ G} (c : cocycles₂ A) (g : G) : c (g, 1) = A.ρ g (c (1, 1)) := by
  have := cocycle_id c g 1 1
  rw [mul_one, mul_one] at this

  exact add_right_cancel this

theorem cocycle_pow_pow (s : G) {A : Rep ℤ G} (c : cocycles₂ A) (i j : ℕ) :
    c (s ^ i, s ^ j) = A.ρ (s ^ i) (c (1, 1)) + (∑ k ∈ Finset.range j, c (s ^ (i + k), s))
      - A.ρ (s ^ i) (psum s c j) := by
  induction j with
  | zero => rw [pow_zero, cocycle_one, Finset.sum_range_zero, psum_zero, map_zero, add_zero, sub_zero]
  | succ j ih =>
    have hid := cocycle_id c (s ^ i) (s ^ j) s
    rw [← pow_add, ← pow_succ] at hid

    have h1 : c (s ^ i, s ^ (j + 1)) = c (s ^ i, s ^ j) + c (s ^ (i + j), s) - A.ρ (s ^ i) (c (s ^ j, s)) := by
      calc c (s ^ i, s ^ (j + 1))
          = (A.ρ (s ^ i) (c (s ^ j, s)) + c (s ^ i, s ^ (j + 1))) - A.ρ (s ^ i) (c (s ^ j, s)) := by abel
        _ = (c (s ^ (i + j), s) + c (s ^ i, s ^ j)) - A.ρ (s ^ i) (c (s ^ j, s)) := by rw [← hid]
        _ = _ := by abel
    rw [h1, ih, Finset.sum_range_succ, psum_succ, map_add]
    abel

noncomputable def normCochain (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (c : G × G → A) : G → A :=
  fun g => A.ρ g (c (1, 1)) - psum s c (cyclicLog s hs hfin g)

theorem cocycle_eq_carry_add_dOne (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (c : cocycles₂ A) (g h : G) :
    c (g, h) = carryFun s hs hfin (cyclicInv s ⇑c) (g, h)
      + (A.ρ g (normCochain s hs hfin ⇑c h) - normCochain s hs hfin ⇑c (g * h) + normCochain s hs hfin ⇑c g) := by
  set n := orderOf s with hn
  set i := cyclicLog s hs hfin g with hi
  set j := cyclicLog s hs hfin h with hj
  have hin : i < n := cyclicLog_lt s hs hfin g
  have hjn : j < n := cyclicLog_lt s hs hfin h
  have hg : s ^ i = g := pow_cyclicLog s hs hfin g
  have hh : s ^ j = h := pow_cyclicLog s hs hfin h

  have hlog : cyclicLog s hs hfin (g * h) = if n ≤ i + j then i + j - n else i + j := by
    have e := cyclicLog_mul s hs hfin g h
    rw [← hi, ← hj, ← hn] at e
    split_ifs at e ⊢ with hle
    · have : (cyclicLog s hs hfin (g * h) : ℤ) = ((i + j - n : ℕ) : ℤ) := by push_cast [Nat.cast_sub hle]; linarith
      exact_mod_cast this
    · have : (cyclicLog s hs hfin (g * h) : ℤ) = ((i + j : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this

  have hc := cocycle_pow_pow s c i j
  rw [hg, hh] at hc
  rw [carryFun_apply, ← hi, ← hj, ← hn, cyclicInv_eq_psum, ← hn]
  simp only [normCochain, hlog, ← hi, ← hj]
  rw [hc, map_sub, show A.ρ g (A.ρ h (c (1, 1))) = A.ρ (g * h) (c (1, 1)) by
    rw [MonoidHom.map_mul]; rfl, ← hg]

  have hsum : (∑ k ∈ Finset.range j, c (s ^ (i + k), s)) = psum s c (i + j) - psum s c i := by
    rw [psum_add]; abel
  rw [hsum]
  split_ifs with hle
  ·
    have hsplit : psum s (⇑c) (i + j) = psum s c n + psum s c (i + j - n) := by
      conv_lhs => rw [show i + j = n + (i + j - n) by omega]
      exact psum_orderOf_add s c _
    rw [hsplit, one_smul, hg]
    abel
  · rw [zero_smul, zero_add, hg]
    abel

theorem rho_cyclicInv (s : G) {A : Rep ℤ G} (c : cocycles₂ A) :
    A.ρ s (cyclicInv s ⇑c) = cyclicInv s ⇑c := by

  have hk : ∀ k : ℕ, A.ρ s (c (s ^ k, s)) = c (s ^ (k + 1), s) + c (s, s ^ k) - c (s, s ^ (k + 1)) := by
    intro k
    have := cocycle_id c s (s ^ k) s
    rw [← pow_succ', ← pow_succ] at this
    calc A.ρ s (c (s ^ k, s))
        = (A.ρ s (c (s ^ k, s)) + c (s, s ^ (k + 1))) - c (s, s ^ (k + 1)) := by abel
      _ = (c (s ^ (k + 1), s) + c (s, s ^ k)) - c (s, s ^ (k + 1)) := by rw [← this]
      _ = _ := by abel
  rw [cyclicInv, map_sum]
  simp_rw [hk]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : (∑ k ∈ Finset.range (orderOf s), c (s ^ (k + 1), s)) = ∑ k ∈ Finset.range (orderOf s), c (s ^ k, s) := by
    have := Finset.sum_range_succ' (fun k => c (s ^ k, s)) (orderOf s)
    rw [Finset.sum_range_succ, pow_orderOf_eq_one, pow_zero] at this
    exact (add_right_cancel this).symm
  have h2 : (∑ k ∈ Finset.range (orderOf s), c (s, s ^ k)) - ∑ k ∈ Finset.range (orderOf s), c (s, s ^ (k + 1)) = 0 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub', pow_zero, pow_orderOf_eq_one, sub_self]
  rw [add_sub_assoc, h2, add_zero, h1]

end Ws26HL2

namespace Ws26HL2
variable {G : Type} [Group G]

noncomputable def rpsum (s : G) {A : Rep ℤ G} (b : A) (m : ℕ) : A := ∑ k ∈ Finset.range m, A.ρ (s ^ k) b

theorem rpsum_add (s : G) {A : Rep ℤ G} (b : A) (i j : ℕ) :
    rpsum s b (i + j) = rpsum s b i + A.ρ (s ^ i) (rpsum s b j) := by
  simp only [rpsum, Finset.sum_range_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add, MonoidHom.map_mul]; rfl

theorem rpsum_orderOf_add (s : G) {A : Rep ℤ G} (b : A) (r : ℕ) :
    rpsum s b (orderOf s + r) = rpsum s b (orderOf s) + rpsum s b r := by
  rw [rpsum_add, pow_orderOf_eq_one, MonoidHom.map_one]; rfl

theorem sum_range_orderOf_shift (s : G) {A : Rep ℤ G} (γ : G → A) :
    (∑ i ∈ Finset.range (orderOf s), γ (s ^ (i + 1))) = ∑ i ∈ Finset.range (orderOf s), γ (s ^ i) := by
  have := Finset.sum_range_succ' (fun k => γ (s ^ k)) (orderOf s)
  rw [Finset.sum_range_succ, pow_orderOf_eq_one, pow_zero] at this
  exact (add_right_cancel this).symm

end Ws26HL2

namespace Ws26HL2
variable {G : Type} [Group G]

theorem cyclicLog_pow (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (m : ℕ) :
    cyclicLog s hs hfin (s ^ m) = m % orderOf s :=
  cyclicLog_eq_of_pow_eq s hs hfin (Nat.mod_lt _ (orderOf_pos_iff.mpr hfin)) (pow_mod_orderOf s m)

theorem carryFun_zsmul (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (k : ℤ) (a : A) : carryFun s hs hfin (k • a) = k • carryFun s hs hfin a := by
  funext p
  obtain ⟨g, h⟩ := p
  rw [Pi.smul_apply, carryFun_apply, carryFun_apply, smul_comm]

theorem H2pi_carry_zsmul (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (k : ℤ) (a : A) (ha : carryFun s hs hfin a ∈ cocycles₂ A)
    (hka : carryFun s hs hfin (k • a) ∈ cocycles₂ A) :
    (H2π A).hom ⟨carryFun s hs hfin (k • a), hka⟩ = k • (H2π A).hom ⟨carryFun s hs hfin a, ha⟩ := by
  rw [← map_zsmul]
  congr 1
  apply Subtype.ext
  show carryFun s hs hfin (k • a) = k • carryFun s hs hfin a
  exact carryFun_zsmul s hs hfin k a

theorem card_carries (n f : ℕ) (hn : 0 < n) :
    ((Finset.range (n / Nat.gcd n f)).filter (fun b => n ≤ f * b % n + f % n)).card = f % n / Nat.gcd n f := by
  set g := Nat.gcd n f with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left f hn
  obtain ⟨n', hn'⟩ : g ∣ n := Nat.gcd_dvd_left n f
  obtain ⟨f', hf'⟩ : g ∣ f := Nat.gcd_dvd_right n f
  have hn'pos : 0 < n' := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hn'; omega
  have hndiv : n / g = n' := by rw [hn', Nat.mul_div_cancel_left _ hgpos]
  have hcop : Nat.Coprime n' f' := by
    have := Nat.coprime_div_gcd_div_gcd (m := n) (n := f) hgpos
    rw [← hg] at this
    conv at this => rw [hn', hf']; rw [Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos]
    exact this
  have hmod : ∀ b, f * b % n = g * (f' * b % n') := by
    intro b; rw [hf', hn', mul_assoc, Nat.mul_mod_mul_left]
  have hfmod : f % n = g * (f' % n') := by rw [hf', hn', Nat.mul_mod_mul_left]
  set r' := f' % n' with hr'
  have hr'lt : r' < n' := Nat.mod_lt _ hn'pos
  have hcond : ∀ b, (n ≤ f * b % n + f % n ↔ n' ≤ f' * b % n' + r') := by
    intro b
    rw [hmod, hfmod, ← mul_add]
    conv_lhs => rw [hn']
    exact Nat.mul_le_mul_left_iff hgpos
  rw [Finset.filter_congr (fun b _ => hcond b), hndiv, hfmod, Nat.mul_div_cancel_left _ hgpos]

  set hmap : ℕ → ℕ := fun b => f' * b % n' with hhmap
  have hinj : Set.InjOn hmap (Finset.range n' : Set ℕ) := by
    intro b₁ hb₁ b₂ hb₂ heq
    rw [Finset.coe_range, Set.mem_Iio] at hb₁ hb₂
    have h1 : f' * b₁ ≡ f' * b₂ [MOD n'] := heq
    have h2 : b₁ ≡ b₂ [MOD n'] := Nat.ModEq.cancel_left_of_coprime hcop h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hb₁ hb₂
  have himage : (Finset.range n').image hmap = Finset.range n' := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨b, -, rfl⟩ := hk
      exact Finset.mem_range.mpr (Nat.mod_lt _ hn'pos)
    · rw [Finset.card_image_of_injOn hinj]
  have hfi : (Finset.range n').filter (fun b => n' ≤ f' * b % n' + r')
      = (Finset.range n').filter (fun b => n' ≤ hmap b + r') := rfl
  rw [hfi, ← Finset.card_image_of_injOn (hinj.mono (by intro x hx; exact Finset.mem_of_mem_filter x hx))]
  have hswap : (Finset.filter (fun b => n' ≤ hmap b + r') (Finset.range n')).image hmap
      = (Finset.image hmap (Finset.range n')).filter (fun k => n' ≤ k + r') := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨b, ⟨hb, hc⟩, rfl⟩; exact ⟨⟨b, hb, rfl⟩, hc⟩
    · rintro ⟨⟨b, hb, rfl⟩, hc⟩; exact ⟨b, ⟨hb, hc⟩, rfl⟩
  rw [hswap, himage]
  have : (Finset.range n').filter (fun k => n' ≤ k + r') = Finset.Ico (n' - r') n' := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  omega

theorem div_gcd_eq (n f : ℕ) (hn : 0 < n) :
    f / Nat.gcd n f = (n / Nat.gcd n f) * (f / n) + f % n / Nat.gcd n f := by
  set g := Nat.gcd n f with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left f hn
  obtain ⟨n', hn'⟩ : g ∣ n := Nat.gcd_dvd_left n f
  obtain ⟨f', hf'⟩ : g ∣ f := Nat.gcd_dvd_right n f
  have hmodf : f % n = g * (f' % n') := by rw [hf', hn', Nat.mul_mod_mul_left]
  have hdivf : f / n = f' / n' := by
    rw [hf', hn']
    exact Nat.mul_div_mul_left _ _ hgpos
  rw [hmodf, hdivf]
  conv_lhs => rw [hf']
  conv_rhs => rw [hn']
  rw [Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos]
  exact (Nat.div_add_mod f' n').symm

end Ws26HL2

end
end groupCohomology

open _root_.groupCohomology _root_.P2MW.S_groupCohomology_exists_carry_H2pi_eq.groupCohomology groupCohomology.Ws26HL2 in
theorem solution {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (c : cocycles₂ A) :
    A.ρ s (cyclicInv s ⇑c) = cyclicInv s ⇑c ∧
    ∃ h : carryFun s hs hfin (cyclicInv s ⇑c) ∈ cocycles₂ A,
      (H2π A).hom ⟨carryFun s hs hfin (cyclicInv s ⇑c), h⟩ = (H2π A).hom c := by
  have hinv := rho_cyclicInv s c
  refine ⟨hinv, carryFun_mem_cocycles2 s hs hfin _ hinv, ?_⟩
  set β := normCochain s hs hfin ⇑c with hβ
  have hfun : carryFun s hs hfin (cyclicInv s ⇑c) = ⇑c - (d₁₂ A).hom β := by
    funext p
    obtain ⟨g, h⟩ := p
    rw [Pi.sub_apply, d₁₂_hom_apply, cocycle_eq_carry_add_dOne s hs hfin c g h]
    abel
  symm
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  show ⇑c - carryFun s hs hfin (cyclicInv s ⇑c) ∈ coboundaries₂ A
  rw [hfun, sub_sub_cancel]
  exact ⟨β, rfl⟩

end S_groupCohomology_exists_carry_H2pi_eq
end P2MW
export P2MW.S_groupCohomology_exists_carry_H2pi_eq (solution)
