-- Prove2me | solution 2 for mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T14:21:46.351598+00:00
-- url     : https://prove2.me/submissions/1cdf3e57-6d81-42bd-b02e-0f7209863ec5

import Mathlib
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Theorems.Thm_mme_3AP_free_no_collision
import Theorems.Thm_mme_CW_q6_regular_primary_hash_large_uniform_family
import Theorems.Thm_mme_CW_q6_eventual_middle_dominates_hash_modulus
import Theorems.Thm_mme_CW_q6_hash_modulus_le_five_mul_Zcount

open MME BigOperators

set_option autoImplicit false


/-- A uniform threshold extracted from the eventual dominance theorem (which is stated
for arbitrary sequences `L, G`). -/
lemma uniform_threshold :
    ∃ N1 : ℕ, ∀ N L G : ℕ, N1 ≤ N → L + G = N → 341 * L < 100 * G →
      400 * (4 * (Nat.choose N G) ^ 2 + 1) ≤ Nat.choose (2 * G) G := by
  classical
  by_contra hcon
  push_neg at hcon
  let bad : ℕ → Prop := fun N => ∃ L G : ℕ, L + G = N ∧ 341 * L < 100 * G ∧
    Nat.choose (2 * G) G < 400 * (4 * (Nat.choose N G) ^ 2 + 1)
  let Lf : ℕ → ℕ := fun N => if h : bad N then Classical.choose h else N
  let Gf : ℕ → ℕ := fun N =>
    if h : bad N then Classical.choose (Classical.choose_spec h) else 0
  have hev := mme_CW_q6_eventual_middle_dominates_hash_modulus Lf Gf
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N1, hN1⟩ := hev
  obtain ⟨N, L, G, hN, hLG, hlt, hbad⟩ := hcon N1
  have hb : bad N := ⟨L, G, hLG, hlt, hbad⟩
  have h1 := hN1 N hN
  have hL : Lf N = Classical.choose hb := by simp only [Lf, dif_pos hb]
  have hG : Gf N = Classical.choose (Classical.choose_spec hb) := by
    simp only [Gf, dif_pos hb]
  rw [hL, hG] at h1
  obtain ⟨h2, h3, h4⟩ := Classical.choose_spec (Classical.choose_spec hb)
  exact absurd (h1 ⟨h2, h3⟩) (not_le.mpr h4)

/-- The one-entry hash family. -/
def singleFamily {N L G : ℕ} (e0 : CWQ6ExactCoupledAddress N L G) :
    CWQ6PrimaryHashFamily N L G 1 1 where
  hHpos := Nat.one_pos
  entry := fun _ => e0
  xInjective := fun p q _ => Subsingleton.elim p q
  yInjective := fun p q _ => Subsingleton.elim p q
  zSameFiber := fun _ _ _ => rfl
  zSeparatesFibers := fun a b _ _ _ => Subsingleton.elim a b
  induced := fun p q _ _ => ⟨Subsingleton.elim p q, Subsingleton.elim _ _⟩

lemma exists_exact_address {N L G : ℕ} (hreg : CWQ6ExactAddressRegularity N L G)
    (hLG : L + G = N) : Nonempty (CWQ6ExactCoupledAddress N L G) := by
  classical
  have hpos : 0 < (cwQ6ExactAddresses N L G).card := by
    rw [hreg.total_card]
    have h1 : 0 < Nat.choose (2 * N) L := Nat.choose_pos (by omega)
    have h2 : 0 < Nat.choose (2 * N - L) L := Nat.choose_pos (by omega)
    have h3 : 0 < Nat.choose (2 * G) G := Nat.choose_pos (by omega)
    positivity
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  unfold cwQ6ExactAddresses at ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact ⟨⟨a, ha⟩⟩

lemma pow2_threeAPFree (m : ℕ) :
    ThreeAPFree (((Finset.range m).image (fun k : ℕ => 2 ^ k) : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc habc
  rw [Finset.mem_coe, Finset.mem_image] at ha hb hc
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  obtain ⟨k, -, rfl⟩ := hc
  have key : ∀ i k j : ℕ, i < k → 2 ^ i + 2 ^ k = 2 ^ j + 2 ^ j → False := by
    intro i k j hik h
    have hik' : 2 ^ i < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hik
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    have h1 : 2 ^ k < 2 ^ (j + 1) := by
      rw [pow_succ]; linarith
    have h2 : 2 ^ (j + 1) < 2 ^ (k + 1) := by
      rw [pow_succ, pow_succ]; linarith
    have h3 : k < j + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
    have h4 : j + 1 < k + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
    omega
  rcases lt_trichotomy i k with hik | hik | hik
  · exact (key i k j hik habc).elim
  · subst hik; linarith
  · exact (key k i j hik (by omega)).elim

lemma ratio_bounds (s M N d : ℕ) (hd : 6 ≤ d) (hMpos : 0 < M) (hsM : 2 * s ≤ M) :
    0 ≤ ((s : ℝ) / M) ^ d / ((N + 1 : ℕ) : ℝ) ^ d ∧
    ((s : ℝ) / M) ^ d / ((N + 1 : ℕ) : ℝ) ^ d ≤ (1 / 2 : ℝ) ^ d ∧
    ((s : ℝ) / M) ^ d / ((N + 1 : ℕ) : ℝ) ^ d ≤ 1 / 64 ∧
    ((s : ℝ) / M) ^ d / ((N + 1 : ℕ) : ℝ) ^ d ≤ (s : ℝ) / M * (1 / 32) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hq0 : 0 ≤ (s : ℝ) / M := by positivity
  have hq : (s : ℝ) / M ≤ 1 / 2 := by
    rw [div_le_iff₀ hMr]
    have : (2 * s : ℝ) ≤ M := by exact_mod_cast hsM
    linarith
  have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ d := by
    apply one_le_pow₀
    exact_mod_cast Nat.succ_pos N
  have hpowd : ((s : ℝ) / M) ^ d ≤ (1 / 2 : ℝ) ^ d := pow_le_pow_left₀ hq0 hq d
  have hdiv : ((s : ℝ) / M) ^ d / ((N + 1 : ℕ) : ℝ) ^ d ≤ ((s : ℝ) / M) ^ d :=
    div_le_self (by positivity) hN1
  refine ⟨by positivity, hdiv.trans hpowd, ?_, ?_⟩
  · have h6 : (1 / 2 : ℝ) ^ d ≤ (1 / 2 : ℝ) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
    have : (1 / 2 : ℝ) ^ 6 = 1 / 64 := by norm_num
    linarith
  · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    subst he
    have h5 : (1 / 2 : ℝ) ^ e ≤ (1 / 2 : ℝ) ^ 5 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have : (1 / 2 : ℝ) ^ 5 = 1 / 32 := by norm_num
    have hpe : ((s : ℝ) / M) ^ e ≤ (1 / 2 : ℝ) ^ e := pow_le_pow_left₀ hq0 hq e
    calc ((s : ℝ) / M) ^ (e + 1) / ((N + 1 : ℕ) : ℝ) ^ (e + 1)
        ≤ ((s : ℝ) / M) ^ (e + 1) := hdiv
      _ = (s : ℝ) / M * ((s : ℝ) / M) ^ e := by ring
      _ ≤ (s : ℝ) / M * (1 / 32) := by
          apply mul_le_mul_of_nonneg_left _ hq0
          linarith

lemma third_aux (X M B H : ℕ) (r : ℝ) (hM : M = 4 * X ^ 2 + 1) (hX : 1 ≤ X)
    (hH : H = B / (8 * M)) (hlarge : 400 * M ≤ B) (_hr0 : 0 ≤ r) (hr : r ≤ 1 / 64) :
    (B : ℝ) * r ≤ 4 * (X : ℝ) ^ 2 * H := by
  have hMpos : 0 < M := by omega
  have hH50 : 50 ≤ H := by
    rw [hH, Nat.le_div_iff_mul_le (by omega)]
    linarith
  have hB : B < 8 * M * (H + 1) := by
    have := Nat.lt_div_mul_add (a := B) (b := 8 * M) (by omega)
    rw [← hH] at this
    linarith
  have hM5 : M ≤ 5 * X ^ 2 := by
    have : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX
    omega
  have hBn : B ≤ 256 * X ^ 2 * H := by
    calc B ≤ 8 * M * (H + 1) := hB.le
      _ ≤ 8 * M * (2 * H) := Nat.mul_le_mul_left _ (by omega)
      _ = 16 * M * H := by ring
      _ ≤ 16 * (5 * X ^ 2) * H := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM5)
      _ ≤ 256 * X ^ 2 * H := Nat.mul_le_mul_right H (by omega)
  have hBr : (B : ℝ) ≤ 256 * (X : ℝ) ^ 2 * H := by exact_mod_cast hBn
  calc (B : ℝ) * r ≤ (B : ℝ) * (1 / 64) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ (256 * (X : ℝ) ^ 2 * H) * (1 / 64) := mul_le_mul_of_nonneg_right hBr (by norm_num)
    _ = 4 * (X : ℝ) ^ 2 * H := by ring

lemma A_aux_a (s Z M A : ℕ) (r : ℝ) (hA : s * Z / (16 * M) ≤ A) (hsz : 32 * M ≤ s * Z)
    (hMpos : 0 < M) (_hr0 : 0 ≤ r) (hr : r ≤ (s : ℝ) / M * (1 / 32)) :
    (Z : ℝ) * r ≤ A := by
  have hq : s * Z < 16 * M * (s * Z / (16 * M) + 1) := by
    have := Nat.lt_div_mul_add (a := s * Z) (b := 16 * M) (by omega)
    linarith
  set q := s * Z / (16 * M) with hqdef
  have hqr : ((s : ℝ) * Z) < 16 * (M : ℝ) * (q + 1) := by exact_mod_cast hq
  have hszr : 32 * (M : ℝ) ≤ s * Z := by exact_mod_cast hsz
  have hAr : (q : ℝ) ≤ A := by exact_mod_cast hA
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hkey : (s : ℝ) * Z / (32 * M) ≤ q := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc (Z : ℝ) * r ≤ (Z : ℝ) * ((s : ℝ) / M * (1 / 32)) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (s : ℝ) * Z / (32 * M) := by field_simp
    _ ≤ q := hkey
    _ ≤ A := hAr

lemma A_aux_b (s Z M A : ℕ) (r : ℝ) (hA : 1 ≤ A) (hsz : s * Z < 32 * M)
    (hMpos : 0 < M) (_hr0 : 0 ≤ r) (hr : r ≤ (s : ℝ) / M * (1 / 32)) :
    (Z : ℝ) * r ≤ A := by
  have hszr : (s : ℝ) * Z < 32 * (M : ℝ) := by exact_mod_cast hsz
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hkey : (s : ℝ) * Z / (32 * M) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc (Z : ℝ) * r ≤ (Z : ℝ) * ((s : ℝ) / M * (1 / 32)) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (s : ℝ) * Z / (32 * M) := by field_simp
    _ ≤ 1 := hkey
    _ ≤ A := hAr

lemma H_le_four_pow (n L G M H : ℕ) (hLG : L + G = n + 1)
    (hH : H = Nat.choose (2 * G) G / (8 * M)) : H ≤ 4 ^ (n + 1) := by
  calc H ≤ Nat.choose (2 * G) G := hH ▸ Nat.div_le_self _ _
    _ ≤ 2 ^ (2 * G) := Nat.choose_le_two_pow _ _
    _ ≤ 2 ^ (2 * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 ^ (n + 1) := by rw [pow_mul]; norm_num

/-- `2 ^ 80`, written as a decimal literal. -/
def C80 : ℕ := 1208925819614629174706176

lemma C80_eq : C80 = 2 ^ 80 := by norm_num [C80]

lemma main_bound (d N L G : ℕ) (hd : 6 ≤ d) (N1 : ℕ)
    (hN1 : ∀ N L G : ℕ, N1 ≤ N → L + G = N → 341 * L < 100 * G →
      400 * (4 * (Nat.choose N G) ^ 2 + 1) ≤ Nat.choose (2 * G) G)
    (hdN1 : 4 * (N1 + 2 * C80) ≤ d)
    (hreg : CWQ6ExactAddressRegularity N L G)
    (hL : 0 < L) (hLG : L + G = N) (hcond : 341 * L < 100 * G)
    (S : Finset ℕ) (hS : S ⊆ Finset.range ((4 * (Nat.choose N G) ^ 2 + 1) / 2))
    (hfree : ThreeAPFree (S : Set ℕ)) (hpos : 0 < S.card) :
    ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily N L G A H,
      H ≤ 4 ^ N ∧
      ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
          ((((S.card : ℝ) / ((4 * (Nat.choose N G) ^ 2 + 1 : ℕ) : ℝ)) ^ d) /
            (((N + 1 : ℕ) : ℝ) ^ d)) ≤ (A : ℝ) ∧
      ((Nat.choose (2 * G) G : ℕ) : ℝ) *
          ((((S.card : ℝ) / ((4 * (Nat.choose N G) ^ 2 + 1 : ℕ) : ℝ)) ^ d) /
            (((N + 1 : ℕ) : ℝ) ^ d)) ≤
        4 * ((Nat.choose N G : ℕ) : ℝ) ^ 2 * (H : ℝ) := by
  classical
  have hXpos : 1 ≤ Nat.choose N G := Nat.choose_pos (by omega)
  have hMpos : 0 < 4 * (Nat.choose N G) ^ 2 + 1 := by omega
  have hsM : 2 * S.card ≤ 4 * (Nat.choose N G) ^ 2 + 1 := by
    have h1 : S.card ≤ (4 * (Nat.choose N G) ^ 2 + 1) / 2 := by
      have := Finset.card_le_card hS
      simpa using this
    have h2 : 2 * ((4 * (Nat.choose N G) ^ 2 + 1) / 2) ≤ 4 * (Nat.choose N G) ^ 2 + 1 :=
      Nat.mul_div_le _ 2
    omega
  obtain ⟨hr0, hr2, hr64, hr32⟩ :=
    ratio_bounds S.card (4 * (Nat.choose N G) ^ 2 + 1) N d hd hMpos hsM
  by_cases hbig : N1 + 2 * C80 ≤ N
  · -- large regime: use the platform theorem
    have hlarge : 400 * (4 * (Nat.choose N G) ^ 2 + 1) ≤ Nat.choose (2 * G) G :=
      hN1 N L G (by omega) hLG hcond
    have hG : 0 < G := by omega
    have hGbig : C80 ≤ G := by
      have hC : C80 = 1208925819614629174706176 := rfl
      omega
    have hXG : G + 1 ≤ Nat.choose N G := by
      calc G + 1 = Nat.choose (G + 1) G := (Nat.choose_succ_self_right G).symm
        _ ≤ Nat.choose N G := Nat.choose_le_choose G (by omega)
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hthird : ∀ H : ℕ,
        H = Nat.choose (2 * G) G / (8 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) →
        ((Nat.choose (2 * G) G : ℕ) : ℝ) *
          ((((S.card : ℝ) / ((4 * (Nat.choose (n + 1) G) ^ 2 + 1 : ℕ) : ℝ)) ^ d) /
            (((n + 1 + 1 : ℕ) : ℝ) ^ d)) ≤
        4 * ((Nat.choose (n + 1) G : ℕ) : ℝ) ^ 2 * (H : ℝ) :=
      fun H hH => third_aux _ _ _ H _ rfl hXpos hH hlarge hr0 hr64
    by_cases hsz : 32 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ≤
        S.card * (Nat.choose (2 * (n + 1)) L * Nat.choose (2 * (n + 1) - L) L)
    · obtain ⟨A, H, ⟨fam⟩, hA, hH⟩ :=
        mme_CW_q6_regular_primary_hash_large_uniform_family hreg hG S hS hfree hlarge
      rw [hreg.z_word_card] at hA
      refine ⟨A, H, fam, H_le_four_pow n L G _ H hLG hH, ?_, hthird H hH⟩
      exact A_aux_a S.card _ _ A _ hA hsz hMpos hr0 hr32
    · push_neg at hsz
      -- a large explicit three-term-progression-free set
      set S' : Finset ℕ := (Finset.range 160).image (fun k : ℕ => 2 ^ k) with hS'def
      have hS'card : S'.card = 160 := by
        rw [hS'def, Finset.card_image_of_injective _ (Nat.pow_right_injective le_rfl)]
        simp
      have hX80 : C80 ≤ Nat.choose (n + 1) G := le_trans hGbig (by omega)
      have hX160 : C80 * C80 ≤ (Nat.choose (n + 1) G) ^ 2 := by
        rw [sq]; exact Nat.mul_le_mul hX80 hX80
      have hMhalf : C80 * C80 ≤ (4 * (Nat.choose (n + 1) G) ^ 2 + 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        linarith
      have hS'range : S' ⊆ Finset.range ((4 * (Nat.choose (n + 1) G) ^ 2 + 1) / 2) := by
        intro x hx
        rw [hS'def, Finset.mem_image] at hx
        obtain ⟨k, hk, rfl⟩ := hx
        rw [Finset.mem_range] at hk ⊢
        calc 2 ^ k ≤ 2 ^ 159 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ < C80 * C80 := by norm_num [C80]
          _ ≤ _ := hMhalf
      obtain ⟨A, H, ⟨fam⟩, hA, hH⟩ :=
        mme_CW_q6_regular_primary_hash_large_uniform_family hreg hG S' hS'range
          (pow2_threeAPFree 160) hlarge
      rw [hreg.z_word_card, hS'card] at hA
      have hM5Z := mme_CW_q6_hash_modulus_le_five_mul_Zcount hLG
      have hA1 : 1 ≤ A := by
        refine le_trans ?_ hA
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      refine ⟨A, H, fam, H_le_four_pow n L G _ H hLG hH, ?_, hthird H hH⟩
      exact A_aux_b S.card _ _ A _ hA1 hsz hMpos hr0 hr32
  · -- small regime: one-entry family
    push_neg at hbig
    obtain ⟨e0⟩ := exists_exact_address hreg hLG
    have h2d : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d = 1 := by
      rw [← mul_pow]; norm_num
    have h4N : 4 * N ≤ d := by
      have hC : C80 = 1208925819614629174706176 := rfl
      omega
    have hZle : Nat.choose (2 * N) L * Nat.choose (2 * N - L) L ≤ 2 ^ d := by
      calc Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
          ≤ 2 ^ (2 * N) * 2 ^ (2 * N - L) :=
            Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
        _ ≤ 2 ^ (2 * N) * 2 ^ (2 * N) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ (4 * N) := by rw [← pow_add]; congr 1; ring
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h4N
    have hBle : Nat.choose (2 * G) G ≤ 2 ^ d := by
      calc Nat.choose (2 * G) G ≤ 2 ^ (2 * G) := Nat.choose_le_two_pow _ _
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hZr : ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) ≤ 2 ^ d := by
      exact_mod_cast hZle
    have hBr : ((Nat.choose (2 * G) G : ℕ) : ℝ) ≤ 2 ^ d := by exact_mod_cast hBle
    have hXr : (1 : ℝ) ≤ ((Nat.choose N G : ℕ) : ℝ) := by exact_mod_cast hXpos
    refine ⟨1, 1, singleFamily e0, Nat.one_le_pow _ _ (by norm_num), ?_, ?_⟩
    · calc ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
            ((((S.card : ℝ) / ((4 * (Nat.choose N G) ^ 2 + 1 : ℕ) : ℝ)) ^ d) /
              (((N + 1 : ℕ) : ℝ) ^ d))
          ≤ (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d := mul_le_mul hZr hr2 hr0 (by positivity)
        _ = 1 := h2d
        _ = ((1 : ℕ) : ℝ) := by norm_num
    · calc ((Nat.choose (2 * G) G : ℕ) : ℝ) *
            ((((S.card : ℝ) / ((4 * (Nat.choose N G) ^ 2 + 1 : ℕ) : ℝ)) ^ d) /
              (((N + 1 : ℕ) : ℝ) ^ d))
          ≤ (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d := mul_le_mul hBr hr2 hr0 (by positivity)
        _ = 1 := h2d
        _ ≤ 4 * ((Nat.choose N G : ℕ) : ℝ) ^ 2 * ((1 : ℕ) : ℝ) := by
            push_cast
            nlinarith


theorem solution :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ A H : ℕ,
            ∃ family : CWQ6PrimaryHashFamily N L G A H,
              H ≤ 4 ^ N ∧
              (Zcount : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                (A : ℝ) ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  obtain ⟨N1, hN1⟩ := uniform_threshold
  refine ⟨4 * (N1 + 2 * C80) + 6, by positivity, ?_⟩
  intro N L G hreg hcond
  intro Zcount Xcount middle Mmod S hS hfree hpos
  exact main_bound _ N L G (by omega) N1 hN1 (by omega) hreg hcond.1 hcond.2.1
    hcond.2.2 S hS hfree hpos
