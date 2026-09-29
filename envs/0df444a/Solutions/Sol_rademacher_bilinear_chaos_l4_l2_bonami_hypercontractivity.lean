-- Prove2me | solution 1 for rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T02:32:00.166673+00:00
-- url     : https://prove2.me/submissions/4aec928a-bfda-4ab4-a325-ee54f6a25c18

import Definitions.Def_matrix_completion_rademacher

open scoped BigOperators Classical

/-!
Proof of `rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity` (node ddd7e198):
degree-2 (bilinear) Rademacher-chaos L⁴↔L² hypercontractivity, Bonami's lemma at d=2.

Reference: R. O'Donnell, *Analysis of Boolean Functions*, §9.1–9.5 (Bonami's Lemma:
a degree-≤k multilinear polynomial of i.i.d. Rademachers is `9^k`-reasonable, i.e.
`E[f⁴] ≤ 9^k (E[f²])²`); equivalently A. Bonami 1970 (Ann. Inst. Fourier 20). The
proof here is the textbook one: a single-coordinate 4th-moment expansion (two-point
base case) tensorized by induction over the cube, with degree projection (k=2 ⇒ 81).

Structure (all sorry-free):
  * `BonamiCube.avg` — uniform average over sign-assignments on a coordinate set,
    encoded by `Finset` membership (members = +1).
  * `BonamiCube.poly` — multilinear polynomial with Fourier coefficients `c`.
  * `BonamiCube.bonami` — the GENERAL Bonami lemma by induction on the coordinate set.
  * `BonamiCube.bilin_eq_poly` — the off-diagonal bilinear chaos is `poly univ c` with
    `c` supported on 2-element sets (`degLE 2`).
  * specialization to the platform's `rademacherExpectation` / `rademacherSign`.
-/

namespace BonamiCube

variable {I : Type*} [DecidableEq I]

/-- Sign of coordinate `i`: +1 if `i ∈ T`, else −1. -/
def sgn (T : Finset I) (i : I) : ℝ := if i ∈ T then 1 else -1

/-- Multilinear monomial (character) for monomial set `A`, at sign-assignment `T`. -/
noncomputable def chi (A T : Finset I) : ℝ := ∏ j ∈ A, sgn T j

/-- Multilinear polynomial with coefficients `c`, supported on subsets of `s`. -/
noncomputable def poly (s : Finset I) (c : Finset I → ℝ) (T : Finset I) : ℝ :=
  ∑ A ∈ s.powerset, c A * chi A T

/-- Uniform average of `F` over all sign-assignments on the coordinate set `s`. -/
noncomputable def avg (s : Finset I) (F : Finset I → ℝ) : ℝ :=
  (1 / 2) ^ s.card * ∑ T ∈ s.powerset, F T

/-- degree ≤ k: coefficients vanish above cardinality k. -/
def degLE (k : ℕ) (c : Finset I → ℝ) : Prop := ∀ A, k < A.card → c A = 0

/-! ### Character / polynomial peeling lemmas -/

lemma sgn_insert_of_ne {i j : I} (T : Finset I) (hij : j ≠ i) :
    sgn (insert i T) j = sgn T j := by
  unfold sgn; by_cases h : j ∈ T <;> simp [Finset.mem_insert, h, hij]

lemma chi_insert_of_subset {i : I} {s A : Finset I} (hi : i ∉ s) (hA : A ⊆ s) (T : Finset I) :
    chi A (insert i T) = chi A T := by
  unfold chi; apply Finset.prod_congr rfl
  intro j hj; exact sgn_insert_of_ne T (fun h => hi (hA (h ▸ hj)))

lemma poly_insert_indep {i : I} {s : Finset I} (hi : i ∉ s) (c : Finset I → ℝ) (T : Finset I) :
    poly s c (insert i T) = poly s c T := by
  unfold poly; apply Finset.sum_congr rfl
  intro A hA; rw [Finset.mem_powerset] at hA; rw [chi_insert_of_subset hi hA]

lemma sgn_insert_self (i : I) (T : Finset I) : sgn (insert i T) i = 1 := by unfold sgn; simp
lemma sgn_notMem {i : I} {T : Finset I} (h : i ∉ T) : sgn T i = -1 := by unfold sgn; simp [h]
lemma chi_insert_eq {i : I} {B : Finset I} (hi : i ∉ B) (T : Finset I) :
    chi (insert i B) T = sgn T i * chi B T := by unfold chi; rw [Finset.prod_insert hi]

lemma poly_peel {i : I} {s : Finset I} (hi : i ∉ s) (c : Finset I → ℝ) (T : Finset I) :
    poly (insert i s) c T = poly s c T + sgn T i * poly s (fun B => c (insert i B)) T := by
  unfold poly
  rw [Finset.powerset_insert]
  have hdisj : Disjoint s.powerset (s.powerset.image (insert i)) := by
    rw [Finset.disjoint_left]; intro A hA hAimg
    rw [Finset.mem_powerset] at hA; rw [Finset.mem_image] at hAimg
    obtain ⟨B, hB, hBeq⟩ := hAimg; rw [Finset.mem_powerset] at hB
    exact hi (hA (by rw [← hBeq]; exact Finset.mem_insert_self i B))
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image (by
    intro U hU V hV hUV; rw [Finset.mem_coe, Finset.mem_powerset] at hU hV
    have := congrArg (Finset.erase · i) hUV
    simpa [Finset.erase_insert (fun h => hi (hU h)),
           Finset.erase_insert (fun h => hi (hV h))] using this)]
  rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl
  intro B hB; rw [Finset.mem_powerset] at hB; rw [chi_insert_eq (fun h => hi (hB h))]; ring

/-! ### Average lemmas -/

lemma avg_congr {s : Finset I} {F G : Finset I → ℝ}
    (h : ∀ T ∈ s.powerset, F T = G T) : avg s F = avg s G := by
  unfold avg; rw [Finset.sum_congr rfl h]
lemma avg_nonneg {s : Finset I} {F : Finset I → ℝ} (h : ∀ T, 0 ≤ F T) : 0 ≤ avg s F := by
  unfold avg; exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun T _ => h T))
lemma avg_add {s : Finset I} (F G : Finset I → ℝ) :
    avg s (fun T => F T + G T) = avg s F + avg s G := by
  unfold avg; rw [Finset.sum_add_distrib]; ring
lemma avg_const_mul {s : Finset I} (a : ℝ) (F : Finset I → ℝ) :
    avg s (fun T => a * F T) = a * avg s F := by unfold avg; rw [← Finset.mul_sum]; ring
lemma avg_cauchy_schwarz {s : Finset I} (g h : Finset I → ℝ) :
    (avg s (fun T => g T * h T)) ^ 2 ≤ avg s (fun T => (g T) ^ 2) * avg s (fun T => (h T) ^ 2) := by
  unfold avg
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s.powerset (fun T => g T) (fun T => h T)
  calc ((1 / 2) ^ s.card * ∑ T ∈ s.powerset, g T * h T) ^ 2
      = ((1 / 2) ^ s.card) ^ 2 * (∑ T ∈ s.powerset, g T * h T) ^ 2 := by ring
    _ ≤ ((1 / 2) ^ s.card) ^ 2 *
          ((∑ T ∈ s.powerset, (g T) ^ 2) * (∑ T ∈ s.powerset, (h T) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = ((1 / 2) ^ s.card * ∑ T ∈ s.powerset, (g T) ^ 2) *
          ((1 / 2) ^ s.card * ∑ T ∈ s.powerset, (h T) ^ 2) := by ring

lemma avg_insert {i : I} {s : Finset I} (hi : i ∉ s) (F : Finset I → ℝ) :
    avg (insert i s) F = avg s (fun T => (F T + F (insert i T)) / 2) := by
  unfold avg
  rw [Finset.powerset_insert, Finset.card_insert_of_notMem hi]
  have hdisj : Disjoint s.powerset (s.powerset.image (insert i)) := by
    rw [Finset.disjoint_left]; intro T hT hTimg
    rw [Finset.mem_powerset] at hT; rw [Finset.mem_image] at hTimg
    obtain ⟨U, hU, hUeq⟩ := hTimg; rw [Finset.mem_powerset] at hU
    exact hi (hT (by rw [← hUeq]; exact Finset.mem_insert_self i U))
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image (by
    intro U hU V hV hUV; rw [Finset.mem_coe, Finset.mem_powerset] at hU hV
    have := congrArg (Finset.erase · i) hUV
    simpa [Finset.erase_insert (fun h => hi (hU h)),
           Finset.erase_insert (fun h => hi (hV h))] using this)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro T _; rw [pow_succ]; ring

/-! ### The two moment-peeling identities -/

lemma leaf_pow4 {i : I} {s : Finset I} (hi : i ∉ s) (c : Finset I → ℝ)
    {T : Finset I} (hiT : i ∉ T) :
    ((poly (insert i s) c T) ^ 4 + (poly (insert i s) c (insert i T)) ^ 4) / 2 =
      (poly s c T) ^ 4
      + 6 * (poly s c T) ^ 2 * (poly s (fun B => c (insert i B)) T) ^ 2
      + (poly s (fun B => c (insert i B)) T) ^ 4 := by
  rw [poly_peel hi c T, poly_peel hi c (insert i T)]
  rw [poly_insert_indep hi c, poly_insert_indep hi (fun B => c (insert i B))]
  rw [sgn_insert_self, sgn_notMem hiT]; ring

lemma leaf_pow2 {i : I} {s : Finset I} (hi : i ∉ s) (c : Finset I → ℝ)
    {T : Finset I} (hiT : i ∉ T) :
    ((poly (insert i s) c T) ^ 2 + (poly (insert i s) c (insert i T)) ^ 2) / 2 =
      (poly s c T) ^ 2 + (poly s (fun B => c (insert i B)) T) ^ 2 := by
  rw [poly_peel hi c T, poly_peel hi c (insert i T)]
  rw [poly_insert_indep hi c, poly_insert_indep hi (fun B => c (insert i B))]
  rw [sgn_insert_self, sgn_notMem hiT]; ring

lemma avg_poly_pow4_peel {i : I} {s : Finset I} (hi : i ∉ s) (c : Finset I → ℝ) :
    avg (insert i s) (fun T => (poly (insert i s) c T) ^ 4) =
      avg s (fun T => (poly s c T) ^ 4
        + 6 * (poly s c T) ^ 2 * (poly s (fun B => c (insert i B)) T) ^ 2
        + (poly s (fun B => c (insert i B)) T) ^ 4) := by
  rw [avg_insert hi]; apply avg_congr; intro T hT
  rw [Finset.mem_powerset] at hT; exact leaf_pow4 hi c (fun h => hi (hT h))

lemma avg_poly_pow2_peel {i : I} {s : Finset I} (hi : i ∉ s) (c : Finset I → ℝ) :
    avg (insert i s) (fun T => (poly (insert i s) c T) ^ 2) =
      avg s (fun T => (poly s c T) ^ 2 + (poly s (fun B => c (insert i B)) T) ^ 2) := by
  rw [avg_insert hi]; apply avg_congr; intro T hT
  rw [Finset.mem_powerset] at hT; exact leaf_pow2 hi c (fun h => hi (hT h))

/-! ### The scalar combine step (the numeric heart of the induction) -/

theorem combine_step (k : ℕ) (hk : 1 ≤ k) (A B P Q R : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hP : P ≤ (9:ℝ)^k * A^2) (hQ : Q ≤ (9:ℝ)^(k-1) * B^2)
    (hPnn : 0 ≤ P) (hQnn : 0 ≤ Q) (hCS : R^2 ≤ P * Q) :
    P + 6 * R + Q ≤ (9:ℝ)^k * (A + B)^2 := by
  have hpow : (9:ℝ)^k = 9 * (9:ℝ)^(k-1) := by
    conv_lhs => rw [show k = (k-1) + 1 from by omega]
    rw [pow_succ]; ring
  have hpownn : (0:ℝ) ≤ (9:ℝ)^(k-1) := by positivity
  have hmono : (9:ℝ)^(k-1) ≤ (9:ℝ)^k := by rw [hpow]; nlinarith [hpownn]
  have hQle : Q ≤ (9:ℝ)^k * B^2 := le_trans hQ (by nlinarith [sq_nonneg B, hmono])
  have hRsq : R^2 ≤ ((9:ℝ)^k * A^2) * ((9:ℝ)^(k-1) * B^2) := by
    calc R^2 ≤ P * Q := hCS
      _ ≤ ((9:ℝ)^k * A^2) * ((9:ℝ)^(k-1) * B^2) := mul_le_mul hP hQ hQnn (by positivity)
  have h6Rsq : (6 * R)^2 ≤ (2 * (9:ℝ)^k * A * B)^2 := by
    have : (2 * (9:ℝ)^k * A * B)^2 = 36 * ((9:ℝ)^k * A^2) * ((9:ℝ)^(k-1) * B^2) := by
      rw [hpow]; ring
    rw [this]; nlinarith [hRsq]
  have h6Rnn : 0 ≤ 2 * (9:ℝ)^k * A * B := by positivity
  have h6R : 6 * R ≤ 2 * (9:ℝ)^k * A * B := (abs_le_of_sq_le_sq' h6Rsq h6Rnn).2
  nlinarith [hP, hQle, h6R, sq_nonneg (A + B)]

/-! ### The general Bonami lemma -/

theorem bonami (s : Finset I) :
    ∀ (k : ℕ) (c : Finset I → ℝ), degLE k c →
      avg s (fun T => (poly s c T) ^ 4) ≤ 9 ^ k * (avg s (fun T => (poly s c T) ^ 2)) ^ 2 := by
  induction s using Finset.induction with
  | empty =>
    intro k c _
    simp only [avg, Finset.card_empty, pow_zero, one_mul, Finset.powerset_empty,
      Finset.sum_singleton]
    have : poly ∅ c ∅ ^ 4 ≤ 9 ^ k * (poly ∅ c ∅ ^ 2) ^ 2 := by
      have h9 : (1:ℝ) ≤ 9 ^ k := one_le_pow₀ (by norm_num)
      nlinarith [sq_nonneg (poly ∅ c ∅ ^ 2), h9]
    convert this using 2 <;> ring
  | @insert i s hi ih =>
    intro k c hc
    set cD : Finset I → ℝ := fun B => if i ∈ B then 0 else c (insert i B) with hcD
    have hcD_eq : ∀ B ⊆ s, cD B = c (insert i B) := by
      intro B hBs; rw [hcD]; simp only; rw [if_neg (fun h => hi (hBs h))]
    have hpolyD : ∀ T, poly s cD T = poly s (fun B => c (insert i B)) T := by
      intro T; unfold poly; apply Finset.sum_congr rfl
      intro B hB; rw [Finset.mem_powerset] at hB; rw [hcD_eq B hB]
    rw [avg_poly_pow4_peel hi, avg_poly_pow2_peel hi]
    simp only [← hpolyD]
    have hsplit4 : avg s (fun T => (poly s c T) ^ 4
        + 6 * (poly s c T) ^ 2 * (poly s cD T) ^ 2 + (poly s cD T) ^ 4) =
        avg s (fun T => (poly s c T) ^ 4)
        + 6 * avg s (fun T => (poly s c T) ^ 2 * (poly s cD T) ^ 2)
        + avg s (fun T => (poly s cD T) ^ 4) := by
      rw [avg_add (fun T => (poly s c T)^4 + 6 * (poly s c T)^2 * (poly s cD T)^2)
            (fun T => (poly s cD T)^4)]
      rw [avg_add (fun T => (poly s c T)^4)
            (fun T => 6 * (poly s c T)^2 * (poly s cD T)^2)]
      rw [show (fun T => 6 * (poly s c T)^2 * (poly s cD T)^2)
            = (fun T => 6 * ((poly s c T)^2 * (poly s cD T)^2)) from by funext T; ring]
      rw [avg_const_mul 6]
    have hsplit2 : avg s (fun T => (poly s c T) ^ 2 + (poly s cD T) ^ 2) =
        avg s (fun T => (poly s c T) ^ 2) + avg s (fun T => (poly s cD T) ^ 2) :=
      avg_add _ _
    rw [hsplit4, hsplit2]
    set A := avg s (fun T => (poly s c T) ^ 2) with hAdef
    set B := avg s (fun T => (poly s cD T) ^ 2) with hBdef
    set P := avg s (fun T => (poly s c T) ^ 4) with hPdef
    set Q := avg s (fun T => (poly s cD T) ^ 4) with hQdef
    set R := avg s (fun T => (poly s c T) ^ 2 * (poly s cD T) ^ 2) with hRdef
    have hAnn : 0 ≤ A := avg_nonneg (fun T => sq_nonneg _)
    have hBnn : 0 ≤ B := avg_nonneg (fun T => sq_nonneg _)
    have hPnn : 0 ≤ P := avg_nonneg (fun T => by positivity)
    have hQnn : 0 ≤ Q := avg_nonneg (fun T => by positivity)
    have hRnn : 0 ≤ R := avg_nonneg (fun T => by positivity)
    have hPbound : P ≤ 9 ^ k * A ^ 2 := ih k c hc
    have hCS : R ^ 2 ≤ P * Q := by
      have hcs := avg_cauchy_schwarz (s := s) (fun T => (poly s c T)^2) (fun T => (poly s cD T)^2)
      have e1 : (avg s fun T => ((poly s c T)^2)^2) = P := by
        rw [hPdef]; apply avg_congr; intro T _; ring
      have e2 : (avg s fun T => ((poly s cD T)^2)^2) = Q := by
        rw [hQdef]; apply avg_congr; intro T _; ring
      rw [e1, e2] at hcs; exact hcs
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hcD0 : ∀ B, cD B = 0 := by
        intro B; rw [hcD]; simp only
        by_cases hiB : i ∈ B
        · rw [if_pos hiB]
        · rw [if_neg hiB]; apply hc
          exact Finset.card_pos.mpr (Finset.insert_nonempty i B)
      have hpolyD0 : ∀ T, poly s cD T = 0 := by
        intro T; unfold poly; apply Finset.sum_eq_zero
        intro Aa _; rw [hcD0 Aa]; ring
      have hzero : avg s (fun _ => (0:ℝ)) = 0 := by simp [avg]
      have hB0 : B = 0 := by
        rw [hBdef, avg_congr (G := fun _ => (0:ℝ)) (by intro T _; rw [hpolyD0]; ring), hzero]
      have hQ0 : Q = 0 := by
        rw [hQdef, avg_congr (G := fun _ => (0:ℝ)) (by intro T _; rw [hpolyD0]; ring), hzero]
      have hR0 : R = 0 := by
        rw [hRdef, avg_congr (G := fun _ => (0:ℝ)) (by intro T _; rw [hpolyD0]; ring), hzero]
      rw [hB0, hQ0, hR0]; simpa using hPbound
    · have hcDdeg : degLE (k - 1) cD := by
        intro B hB; rw [hcD]; simp only
        by_cases hiB : i ∈ B
        · rw [if_pos hiB]
        · rw [if_neg hiB]; apply hc
          rw [Finset.card_insert_of_notMem hiB]; omega
      have hQbound : Q ≤ 9 ^ (k-1) * B ^ 2 := ih (k-1) cD hcDdeg
      exact combine_step k hk1 A B P Q R hAnn hBnn hRnn hPbound hQbound hPnn hQnn hCS

/-! ### Bridge: the off-diagonal bilinear chaos is `poly univ c` with `degLE 2` -/

variable [Fintype I]

lemma chi_pair {w₁ w₂ : I} (h : w₁ ≠ w₂) (T : Finset I) :
    chi {w₁, w₂} T = sgn T w₁ * sgn T w₂ := by unfold chi; rw [Finset.prod_pair h]

noncomputable def bilinCoeff (a : I → I → ℝ) (A : Finset I) : ℝ :=
  ∑ w₁ : I, ∑ w₂ : I, if w₁ ≠ w₂ ∧ ({w₁, w₂} : Finset I) = A then a w₁ w₂ else 0

lemma bilinCoeff_degLE2 (a : I → I → ℝ) : degLE 2 (bilinCoeff a) := by
  intro A hA
  unfold bilinCoeff
  apply Finset.sum_eq_zero; intro w₁ _
  apply Finset.sum_eq_zero; intro w₂ _
  rw [if_neg]
  rintro ⟨_, hAeq⟩
  rw [← hAeq] at hA
  have : ({w₁, w₂} : Finset I).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega

lemma bilin_eq_poly (a : I → I → ℝ) (T : Finset I) :
    (∑ w₁ : I, ∑ w₂ : I,
      (if w₁ = w₂ then (0:ℝ) else a w₁ w₂ * sgn T w₁ * sgn T w₂)) =
    poly Finset.univ (bilinCoeff a) T := by
  unfold poly bilinCoeff
  have step1 : (∑ A ∈ (Finset.univ : Finset I).powerset,
        (∑ w₁ : I, ∑ w₂ : I, if w₁ ≠ w₂ ∧ ({w₁,w₂}:Finset I) = A then a w₁ w₂ else 0) * chi A T)
        = ∑ A ∈ (Finset.univ : Finset I).powerset, ∑ w₁ : I, ∑ w₂ : I,
            (if w₁ ≠ w₂ ∧ ({w₁,w₂}:Finset I) = A then a w₁ w₂ else 0) * chi A T := by
    apply Finset.sum_congr rfl; intro A _; rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro w₁ _; rw [Finset.sum_mul]
  rw [step1]; symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w₂ _
  by_cases hne : w₁ = w₂
  · simp only [if_pos hne]
    apply Finset.sum_eq_zero; intro A _
    rw [if_neg (by rintro ⟨h, _⟩; exact h hne)]; ring
  · rw [if_neg hne]
    rw [Finset.sum_eq_single ({w₁, w₂} : Finset I)]
    · rw [if_pos ⟨hne, rfl⟩, chi_pair hne]; ring
    · intro A _ hA; rw [if_neg (by rintro ⟨_, h⟩; exact hA h.symm)]; ring
    · intro hnot; exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) hnot

/-! ### Average ↔ rademacherExpectation on the full cube -/

lemma avg_univ_eq_radExp {n1 n2 : ℕ} (F : Finset (Fin n1 × Fin n2) → ℝ) :
    avg (Finset.univ : Finset (Fin n1 × Fin n2)) F =
      MatrixCompletion.rademacherExpectation (n1 := n1) (n2 := n2) F := by
  unfold avg MatrixCompletion.rademacherExpectation MatrixCompletion.rademacherObservationWeight
  rw [Finset.powerset_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.card_univ]

lemma sgn_eq_radSign {n1 n2 : ℕ} (eps : Finset (Fin n1 × Fin n2)) (w : Fin n1 × Fin n2) :
    sgn eps w = MatrixCompletion.rademacherSign eps w.1 w.2 := by
  unfold sgn MatrixCompletion.rademacherSign
  congr 1

end BonamiCube

open MatrixCompletion

/-- The platform target node ddd7e198. -/
theorem solution
    {n₁ n₂ : ℕ} (a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ) :
    rademacherExpectation (n1 := n₁) (n2 := n₂)
        (fun eps =>
          (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
            (if w1 = w2 then (0 : ℝ)
             else a w1 w2 * rademacherSign eps w1.1 w1.2
                          * rademacherSign eps w2.1 w2.2)) ^ 4) ≤
      81 * (rademacherExpectation (n1 := n₁) (n2 := n₂)
              (fun eps =>
                (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                  (if w1 = w2 then (0 : ℝ)
                   else a w1 w2 * rademacherSign eps w1.1 w1.2
                                * rademacherSign eps w2.1 w2.2)) ^ 2)) ^ 2 := by
  -- rewrite rademacherSign → BonamiCube.sgn and the chaos → poly univ (bilinCoeff a)
  have hchaos : ∀ eps : Finset (Fin n₁ × Fin n₂),
      (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
        (if w1 = w2 then (0 : ℝ)
         else a w1 w2 * rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)) =
      BonamiCube.poly Finset.univ (BonamiCube.bilinCoeff a) eps := by
    intro eps
    rw [← BonamiCube.bilin_eq_poly a eps]
    apply Finset.sum_congr rfl; intro w1 _
    apply Finset.sum_congr rfl; intro w2 _
    by_cases h : w1 = w2
    · simp [h]
    · rw [if_neg h, if_neg h]
      rw [BonamiCube.sgn_eq_radSign, BonamiCube.sgn_eq_radSign]
  -- rewrite both expectations
  simp only [hchaos]
  rw [← BonamiCube.avg_univ_eq_radExp, ← BonamiCube.avg_univ_eq_radExp]
  -- apply general Bonami at k = 2; 9^2 = 81
  have hbon := BonamiCube.bonami (Finset.univ : Finset (Fin n₁ × Fin n₂)) 2
      (BonamiCube.bilinCoeff a) (BonamiCube.bilinCoeff_degLE2 a)
  calc BonamiCube.avg Finset.univ (fun T => (BonamiCube.poly Finset.univ (BonamiCube.bilinCoeff a) T) ^ 4)
      ≤ 9 ^ 2 * (BonamiCube.avg Finset.univ
          (fun T => (BonamiCube.poly Finset.univ (BonamiCube.bilinCoeff a) T) ^ 2)) ^ 2 := hbon
    _ = 81 * (BonamiCube.avg Finset.univ
          (fun T => (BonamiCube.poly Finset.univ (BonamiCube.bilinCoeff a) T) ^ 2)) ^ 2 := by norm_num
