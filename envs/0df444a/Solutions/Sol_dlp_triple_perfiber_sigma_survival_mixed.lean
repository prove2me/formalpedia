-- Prove2me | solution 1 for dlp_triple_perfiber_sigma_survival_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-24T03:09:10.063143+00:00
-- url     : https://prove2.me/submissions/973300a1-35b1-4f44-956f-090df91efd99

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Definitions.Def_matrix_completion_bernoulli
import Theorems.Thm_spectral_norm_dual_attainment
import Theorems.Thm_spectral_norm_inner_pairing_bound
import Theorems.Thm_rademacher_expectation_eq_bernoulli_half_expectation
import Theorems.Thm_bernoulli_powerset_expectation_double
import Theorems.Thm_bernoulli_powerset_expectation_pair_coordinate
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Theorems.Thm_bernoulli_powerset_expectation_linear
import Theorems.Thm_bernoulli_powerset_expectation_prod_factor
import Theorems.Thm_dlp_conditional_lemma2_sigma_fiber_mixed3_chaos_inl
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 eq (6): the TOTAL
hypothesis-free per-fiber σ-survival lower bound on the concrete matrix MIXED
(linear + bilinear + trilinear, degree-≤3) chaos.

Order-3 analog of `dlp_pair_perfiber_sigma_survival_mixed` (db8a020b). The dlP order-3
forward bound applies Lemma 2 (eq 6) with the mean-zero σ-fluctuation
`ξ_σ = 8·decoupled(Z_σ) − T_{n,3}`, which carries generically-nonzero LINEAR (r=1) and
BILINEAR (r=2) terms in addition to the trilinear (r=3) term — exactly dlP Lemma 2's
degree-≤k tetrahedral chaos `Σ_{r=1}^k`.

Composes the Proved pieces:
  • norming-pair existence (06fa187a, spectral_norm_dual_attainment);
  • mean-0 of the σ-chaos dual image: LINEAR via single-coordinate marginal (740c5573),
    BILINEAR via pair-coordinate marginal (e1573ddf) + double linearity (726fbda4),
    TRILINEAR via triple-coordinate factorization (derived inline from prod_factor ba91ff06)
    + triple linearity (derived inline), σ-fiber bridge a2fb59eb;
  • CASE SPLIT on E_σ[F²]:
      – 0 < E_σ[F²]  → dlp_conditional_lemma2_sigma_fiber_mixed3_chaos_inl (mixed order-3 cond Lemma 2, 1/2916);
      – E_σ[F²] = 0  → inline degenerate branch (pairing splits linearly, survival ≡ 1).
Source: dlP–MS 1995, §4, eq (6) p.5 + Lemma 2; constant 1/2916 = 1/(4·729).
-/

namespace Mixed3PerFiberSurvival

/-- Single-sum linearity of the Bernoulli powerset expectation (push a finite sum
through the expectation). -/
theorem bexp_sum_pushthrough {n₁ n₂ : ℕ} {ι : Type*} [Fintype ι] (p : ℝ)
    (F : ι → Finset (Fin n₁ × Fin n₂) → ℝ) :
    bernoulliExpectation p (fun Omega => ∑ i : ι, F i Omega) =
      ∑ i : ι, bernoulliExpectation p (fun Omega => F i Omega) := by
  classical
  unfold bernoulliExpectation
  have hdist : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * (∑ i : ι, F i Omega) =
        ∑ i : ι, bernoulliObservationWeight p Omega * F i Omega := by
    intro Omega; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun Omega _ => hdist Omega), Finset.sum_comm]

/-- Triple-coordinate factorization (independence) for 3 *distinct* coordinates,
derived from the product-factorization lemma `bernoulli_powerset_expectation_prod_factor`. -/
theorem triple_coordinate {n₁ n₂ : ℕ} (p : ℝ)
    (w1 w2 w3 : Fin n₁ × Fin n₂) (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (g h k : ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => g (if w1 ∈ Omega then 1 else 0) * h (if w2 ∈ Omega then 1 else 0)
                       * k (if w3 ∈ Omega then 1 else 0)) =
      (p * g 1 + (1 - p) * g 0) * (p * h 1 + (1 - p) * h 0) * (p * k 1 + (1 - p) * k 0) := by
  classical
  set F : (Fin n₁ × Fin n₂) → ℝ → ℝ :=
    fun u => if u = w1 then g else if u = w2 then h else if u = w3 then k else (fun _ => 1) with hF
  have key := bernoulli_powerset_expectation_prod_factor (n₁ := n₁) (n₂ := n₂) p F
  have collapse : ∀ (φ : (Fin n₁ × Fin n₂) → ℝ) (c1 c2 c3 : ℝ),
      (∀ u, u ≠ w1 → u ≠ w2 → u ≠ w3 → φ u = 1) → φ w1 = c1 → φ w2 = c2 → φ w3 = c3 →
      (∏ u : Fin n₁ × Fin n₂, φ u) = c1 * c2 * c3 := by
    intro φ c1 c2 c3 hother hw1 hw2 hw3
    rw [← Finset.prod_mul_prod_compl ({w1, w2, w3} : Finset (Fin n₁ × Fin n₂)) φ]
    have h1 : (∏ u ∈ ({w1, w2, w3} : Finset (Fin n₁ × Fin n₂)), φ u) = c1 * c2 * c3 := by
      rw [Finset.prod_insert (by simp [h12, h13]), Finset.prod_pair h23, hw1, hw2, hw3]; ring
    have h2 : (∏ u ∈ ({w1, w2, w3} : Finset (Fin n₁ × Fin n₂))ᶜ, φ u) = 1 := by
      apply Finset.prod_eq_one
      intro u hu
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
      exact hother u hu.1 hu.2.1 hu.2.2
    rw [h1, h2, mul_one]
  have hL : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        ∏ u : Fin n₁ × Fin n₂, F u (if u ∈ Omega then 1 else 0)) =
      (fun Omega => g (if w1 ∈ Omega then 1 else 0) * h (if w2 ∈ Omega then 1 else 0)
                     * k (if w3 ∈ Omega then 1 else 0)) := by
    funext Omega
    apply collapse (fun u => F u (if u ∈ Omega then 1 else 0))
    · intro u hu1 hu2 hu3; simp only [hF, if_neg hu1, if_neg hu2, if_neg hu3]
    · simp only [hF, if_pos rfl]
    · simp only [hF, if_neg (show w2 ≠ w1 from fun he => h12 he.symm), if_true]
    · simp only [hF, if_neg (show w3 ≠ w1 from fun he => h13 he.symm),
        if_neg (show w3 ≠ w2 from fun he => h23 he.symm), if_true]
  rw [hL] at key
  rw [key]
  apply collapse (fun u => p * F u 1 + (1 - p) * F u 0)
  · intro u hu1 hu2 hu3; simp only [hF, if_neg hu1, if_neg hu2, if_neg hu3]; ring
  · simp only [hF, if_pos rfl]
  · simp only [hF, if_neg (show w2 ≠ w1 from fun he => h12 he.symm), if_true]
  · simp only [hF, if_neg (show w3 ≠ w1 from fun he => h13 he.symm),
      if_neg (show w3 ≠ w2 from fun he => h23 he.symm), if_true]

/-- The MIXED degree-≤3 matrix-valued σ-sign chaos. -/
noncomputable def mchaos3 {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (cc : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (eps : Finset (Fin n1 × Fin n2)) : RealMatrix n1 n2 :=
  (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
  + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
      (if w1 = w2 then (0 : RealMatrix n1 n2)
       else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
  + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
       else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
              * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))

end Mixed3PerFiberSurvival

open Mixed3PerFiberSurvival

theorem solution
    {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (cc : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                        * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))))
          then (1 : ℝ) else 0) ≥ 1 / 2916 := by
  classical
  obtain ⟨xv, yv, hxv, hyv, hnorm⟩ := spectral_norm_dual_attainment T
  set F : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => ⟪Matrix.toEuclideanLin (mchaos3 b a cc eps) xv, yv⟫_ℝ with hF
  set bc : (Fin n1 × Fin n2) → ℝ :=
    fun w => ⟪Matrix.toEuclideanLin (b w) xv, yv⟫_ℝ with hbc
  set ac : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 => ⟪Matrix.toEuclideanLin (a w1 w2) xv, yv⟫_ℝ with hac
  set ccc : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 w3 => ⟪Matrix.toEuclideanLin (cc w1 w2 w3) xv, yv⟫_ℝ with hccc
  -- F is the off-diagonal scalar MIXED degree-≤3 sign-chaos with coefficients (bc, ac, ccc).
  have hFchaos :
      ∀ eps,
        F eps =
          (∑ w : Fin n1 × Fin n2, bc w * rademacherSign eps w.1 w.2)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : ℝ)
                 else ac w1 w2 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2))
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
                 else ccc w1 w2 w3 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2
                              * rademacherSign eps w3.1 w3.2)) := by
    intro eps
    simp only [hF, mchaos3]
    rw [map_add, LinearMap.add_apply, inner_add_left]
    rw [map_add, LinearMap.add_apply, inner_add_left]
    congr 1
    congr 1
    · rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [map_smul, LinearMap.smul_apply, inner_smul_left]
      simp only [hbc, conj_trivial]; ring
    · rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w1 _ => ?_)
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w2 _ => ?_)
      by_cases h : w1 = w2
      · simp [h]
      · simp only [if_neg h]
        rw [map_smul, LinearMap.smul_apply, inner_smul_left]
        simp only [hac, conj_trivial]; ring
    · rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w1 _ => ?_)
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w2 _ => ?_)
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w3 _ => ?_)
      by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
      · simp [h]
      · simp only [if_neg h]
        rw [map_smul, LinearMap.smul_apply, inner_smul_left]
        simp only [hccc, conj_trivial]; ring
  -- helper: rademacherSign eps w = 2·ind − 1
  have hsgn : ∀ (eps : Finset (Fin n1 × Fin n2)) (w : Fin n1 × Fin n2),
      rademacherSign eps w.1 w.2 = 2 * (if w ∈ eps then (1:ℝ) else 0) - 1 := by
    intro eps w
    unfold rademacherSign
    by_cases hm : (w.1, w.2) ∈ eps
    · have : w ∈ eps := by simpa using hm
      simp [hm, this]; norm_num
    · have : w ∉ eps := by simpa using hm
      simp [hm, this]
  -- MEAN-0: linear + bilinear + trilinear halves all vanish under σ.
  have hmean : rademacherExpectation F = 0 := by
    set L : Finset (Fin n1 × Fin n2) → ℝ :=
      fun eps => ∑ w : Fin n1 × Fin n2, bc w * rademacherSign eps w.1 w.2 with hL
    set Bl : Finset (Fin n1 × Fin n2) → ℝ :=
      fun eps => ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
        (if w1 = w2 then (0 : ℝ)
         else ac w1 w2 * rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) with hBl
    set Tl : Finset (Fin n1 × Fin n2) → ℝ :=
      fun eps => ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
         else ccc w1 w2 w3 * rademacherSign eps w1.1 w1.2
                  * rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2) with hTl
    have hFsplit : F = (fun eps => L eps + Bl eps + Tl eps) := by funext eps; rw [hFchaos eps]
    have hadd : rademacherExpectation (fun eps => L eps + Bl eps + Tl eps)
        = rademacherExpectation L + rademacherExpectation Bl + rademacherExpectation Tl := by
      unfold rademacherExpectation
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro eps _; ring
    -- LINEAR half = 0
    have hLmean : rademacherExpectation L = 0 := by
      have hLind : L = (fun eps =>
          ∑ w : Fin n1 × Fin n2,
            (fun (w : Fin n1 × Fin n2) (x : ℝ) => bc w * (2 * x - 1))
              w (if w ∈ eps then (1:ℝ) else 0)) := by
        funext eps; rw [hL]
        apply Finset.sum_congr rfl; intro w _; rw [hsgn]
      rw [hLind, rademacher_expectation_eq_bernoulli_half_expectation]
      rw [bernoulli_powerset_expectation_linear ((1:ℝ)/2)
        (fun (w : Fin n1 × Fin n2) (x : ℝ) => bc w * (2 * x - 1))]
      apply Finset.sum_eq_zero; intro w _; norm_num
    -- BILINEAR half = 0
    have hBmean : rademacherExpectation Bl = 0 := by
      set G : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ → ℝ → ℝ :=
        fun w1 w2 x y =>
          if w1 = w2 then (0 : ℝ) else ac w1 w2 * (2 * x - 1) * (2 * y - 1) with hG
      have hBind : Bl = (fun eps =>
          ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            G w1 w2 (if w1 ∈ eps then (1:ℝ) else 0) (if w2 ∈ eps then (1:ℝ) else 0)) := by
        funext eps; rw [hBl]
        refine Finset.sum_congr rfl (fun w1 _ => ?_)
        refine Finset.sum_congr rfl (fun w2 _ => ?_)
        by_cases h : w1 = w2
        · simp [hG, h]
        · simp only [hG, if_neg h]; rw [hsgn, hsgn]
      rw [hBind, rademacher_expectation_eq_bernoulli_half_expectation]
      rw [bernoulli_powerset_expectation_double]
      apply Finset.sum_eq_zero; intro w1 _
      apply Finset.sum_eq_zero; intro w2 _
      by_cases h : w1 = w2
      · have hz : (fun Omega : Finset (Fin n1 × Fin n2) =>
            G w1 w2 (if w1 ∈ Omega then (1:ℝ) else 0)
            (if w2 ∈ Omega then (1:ℝ) else 0)) = (fun _ => (0:ℝ)) := by
          funext Omega; simp [hG, h]
        rw [hz]; simp [bernoulliExpectation]
      · have hpair := bernoulli_powerset_expectation_pair_coordinate
          ((1:ℝ)/2) w1 w2 h (fun x => ac w1 w2 * (2 * x - 1)) (fun y => 2 * y - 1)
        have hbody :
            (fun Omega : Finset (Fin n1 × Fin n2) =>
                G w1 w2 (if w1 ∈ Omega then (1:ℝ) else 0)
                (if w2 ∈ Omega then (1:ℝ) else 0))
            = (fun Omega : Finset (Fin n1 × Fin n2) =>
                (fun x => ac w1 w2 * (2 * x - 1)) (if w1 ∈ Omega then (1:ℝ) else 0)
                * (fun y => 2 * y - 1) (if w2 ∈ Omega then (1:ℝ) else 0)) := by
          funext Omega; simp only [hG, if_neg h]
        rw [hbody, hpair]; norm_num
    -- TRILINEAR half = 0
    have hTmean : rademacherExpectation Tl = 0 := by
      set H : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ → ℝ → ℝ → ℝ :=
        fun w1 w2 w3 x y z =>
          if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
          else ccc w1 w2 w3 * (2 * x - 1) * (2 * y - 1) * (2 * z - 1) with hH
      have hTind : Tl = (fun eps =>
          ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            H w1 w2 w3 (if w1 ∈ eps then (1:ℝ) else 0) (if w2 ∈ eps then (1:ℝ) else 0)
              (if w3 ∈ eps then (1:ℝ) else 0)) := by
        funext eps; rw [hTl]
        refine Finset.sum_congr rfl (fun w1 _ => ?_)
        refine Finset.sum_congr rfl (fun w2 _ => ?_)
        refine Finset.sum_congr rfl (fun w3 _ => ?_)
        by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
        · simp [hH, h]
        · simp only [hH, if_neg h]; rw [hsgn, hsgn, hsgn]
      rw [hTind, rademacher_expectation_eq_bernoulli_half_expectation]
      -- triple linearity: push the 3 sums through the expectation
      rw [bexp_sum_pushthrough ((1:ℝ)/2)
        (fun w1 Omega => ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          H w1 w2 w3 (if w1 ∈ Omega then 1 else 0) (if w2 ∈ Omega then 1 else 0)
            (if w3 ∈ Omega then 1 else 0))]
      apply Finset.sum_eq_zero; intro w1 _
      rw [bexp_sum_pushthrough ((1:ℝ)/2)
        (fun w2 Omega => ∑ w3 : Fin n1 × Fin n2,
          H w1 w2 w3 (if w1 ∈ Omega then 1 else 0) (if w2 ∈ Omega then 1 else 0)
            (if w3 ∈ Omega then 1 else 0))]
      apply Finset.sum_eq_zero; intro w2 _
      rw [bexp_sum_pushthrough ((1:ℝ)/2)
        (fun w3 Omega =>
          H w1 w2 w3 (if w1 ∈ Omega then 1 else 0) (if w2 ∈ Omega then 1 else 0)
            (if w3 ∈ Omega then 1 else 0))]
      apply Finset.sum_eq_zero; intro w3 _
      by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
      · have hz : (fun Omega : Finset (Fin n1 × Fin n2) =>
            H w1 w2 w3 (if w1 ∈ Omega then (1:ℝ) else 0) (if w2 ∈ Omega then (1:ℝ) else 0)
              (if w3 ∈ Omega then (1:ℝ) else 0)) = (fun _ => (0:ℝ)) := by
          funext Omega; simp [hH, h]
        rw [hz]; simp [bernoulliExpectation]
      · push_neg at h
        obtain ⟨h12, h13, h23⟩ := h
        have htrip := triple_coordinate ((1:ℝ)/2) w1 w2 w3 h12 h13 h23
          (fun x => ccc w1 w2 w3 * (2 * x - 1)) (fun y => 2 * y - 1) (fun z => 2 * z - 1)
        have hbody :
            (fun Omega : Finset (Fin n1 × Fin n2) =>
                H w1 w2 w3 (if w1 ∈ Omega then (1:ℝ) else 0) (if w2 ∈ Omega then (1:ℝ) else 0)
                  (if w3 ∈ Omega then (1:ℝ) else 0))
            = (fun Omega : Finset (Fin n1 × Fin n2) =>
                (fun x => ccc w1 w2 w3 * (2 * x - 1)) (if w1 ∈ Omega then (1:ℝ) else 0)
                * (fun y => 2 * y - 1) (if w2 ∈ Omega then (1:ℝ) else 0)
                * (fun z => 2 * z - 1) (if w3 ∈ Omega then (1:ℝ) else 0)) := by
          funext Omega
          simp only [hH, if_neg (by tauto : ¬(w1 = w2 ∨ w1 = w3 ∨ w2 = w3))]
        rw [hbody, htrip]; norm_num
    rw [hFsplit, hadd, hLmean, hBmean, hTmean]; ring
  -- CASE SPLIT on the σ-variance of F.
  by_cases hvar : 0 < rademacherExpectation (fun eps => (F eps) ^ 2)
  · -- positive variance: order-3 mixed conditional Lemma 2
    have := dlp_conditional_lemma2_sigma_fiber_mixed3_chaos_inl b a cc T xv yv hxv hyv hnorm
      (by simpa [hF, mchaos3] using hmean)
      (by simpa [hF, mchaos3] using hvar)
    simpa [mchaos3] using this
  · -- degenerate variance: E[F²] = 0 ⇒ each F eps = 0 ⇒ survival indicator ≡ 1
    push_neg at hvar
    have hsum0 : rademacherExpectation (fun eps => (F eps) ^ 2) = 0 := by
      have hnn : 0 ≤ rademacherExpectation (fun eps => (F eps) ^ 2) := by
        unfold rademacherExpectation rademacherObservationWeight
        apply Finset.sum_nonneg; intro eps _; positivity
      linarith
    have hterm0 : ∀ eps : Finset (Fin n1 × Fin n2), F eps = 0 := by
      intro eps
      have hz : rademacherObservationWeight eps * (F eps) ^ 2 = 0 := by
        have hsumnn : ∀ e : Finset (Fin n1 × Fin n2),
            e ∈ (Finset.univ : Finset (Finset (Fin n1 × Fin n2))) →
            0 ≤ rademacherObservationWeight e * (F e) ^ 2 := by
          intro e _; unfold rademacherObservationWeight; positivity
        have := (Finset.sum_eq_zero_iff_of_nonneg hsumnn).mp
          (by simpa [rademacherExpectation] using hsum0)
        exact this eps (Finset.mem_univ eps)
      have hw : (0:ℝ) < rademacherObservationWeight eps := by
        unfold rademacherObservationWeight; positivity
      have : (F eps) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (ne_of_gt hw)
        · exact h
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hsurv : ∀ eps : Finset (Fin n1 × Fin n2),
        spectralNorm T ≤ spectralNorm (T + mchaos3 b a cc eps) := by
      intro eps
      rw [← hnorm]
      have hFe0 : F eps = 0 := hterm0 eps
      have hsplit :
          ⟪Matrix.toEuclideanLin (T + mchaos3 b a cc eps) xv, yv⟫_ℝ
            = ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ + F eps := by
        simp only [hF, map_add]
        rw [LinearMap.add_apply, inner_add_left]
      have hub :
          ⟪Matrix.toEuclideanLin (T + mchaos3 b a cc eps) xv, yv⟫_ℝ
            ≤ spectralNorm (T + mchaos3 b a cc eps) * ‖xv‖ * ‖yv‖ :=
        spectral_norm_inner_pairing_bound (T + mchaos3 b a cc eps) xv yv
      have hsp_nonneg : 0 ≤ spectralNorm (T + mchaos3 b a cc eps) := by
        rw [spectralNorm]; exact norm_nonneg _
      have hle1 :
          ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ
            ≤ ⟪Matrix.toEuclideanLin (T + mchaos3 b a cc eps) xv, yv⟫_ℝ := by
        rw [hsplit, hFe0]; linarith
      calc ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ
          ≤ ⟪Matrix.toEuclideanLin (T + mchaos3 b a cc eps) xv, yv⟫_ℝ := hle1
        _ ≤ spectralNorm (T + mchaos3 b a cc eps) * ‖xv‖ * ‖yv‖ := hub
        _ ≤ spectralNorm (T + mchaos3 b a cc eps) * 1 * 1 := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hxv hsp_nonneg
              · exact hyv
              · exact norm_nonneg _
              · positivity
        _ = spectralNorm (T + mchaos3 b a cc eps) := by ring
    have hval : rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T + mchaos3 b a cc eps)
          then (1 : ℝ) else 0) = 1 := by
      unfold rademacherExpectation rademacherObservationWeight
      have hterm : ∀ eps : Finset (Fin n1 × Fin n2),
          ((1:ℝ)/2) ^ Fintype.card (Fin n1 × Fin n2)
            * (if spectralNorm T ≤ spectralNorm (T + mchaos3 b a cc eps) then (1:ℝ) else 0)
            = ((1:ℝ)/2) ^ Fintype.card (Fin n1 × Fin n2) := by
        intro eps; rw [if_pos (hsurv eps)]; ring
      rw [Finset.sum_congr rfl (fun eps _ => hterm eps)]
      rw [Finset.sum_const, Finset.card_univ]
      rw [nsmul_eq_mul]
      have hcard : (Fintype.card (Finset (Fin n1 × Fin n2)) : ℝ)
          = 2 ^ Fintype.card (Fin n1 × Fin n2) := by
        rw [Fintype.card_finset]; push_cast; ring
      rw [hcard]
      rw [← mul_pow]; norm_num
    have hgoal :
        rademacherExpectation
            (fun eps =>
              if spectralNorm T ≤ spectralNorm (T + mchaos3 b a cc eps)
              then (1 : ℝ) else 0) ≥ 1 / 2916 := by rw [hval]; norm_num
    exact hgoal
