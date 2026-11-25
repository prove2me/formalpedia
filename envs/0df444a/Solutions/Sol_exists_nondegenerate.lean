-- Prove2me | solution 1 for exists_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:46.962819+00:00
-- url     : https://prove2.me/submissions/cc7bc46d-1a8c-4bad-be44-4df38e966a48

import Definitions.Def_Formalism_PeriodIntegrals_NormGramAtOrigin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrthogonalFamilyExistence_ExistsOrthFamily
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_NormGramAtOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private lemma hform_add_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y + z) = PI.NormGramAtOrigin.hform σ J x y + PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private lemma hform_smul_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    PI.NormGramAtOrigin.hform σ J x (c • y) = c * PI.NormGramAtOrigin.hform σ J x y := by
  simp only [PI.NormGramAtOrigin.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma hform_sum_right' {E : Type} [Field E] (σ : E →+* E) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (f : Fin k → Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (∑ a, f a) = ∑ a, PI.NormGramAtOrigin.hform σ J x (f a) := by
  simp only [PI.NormGramAtOrigin.hform, Finset.sum_apply, Finset.mul_sum]
  calc _ = ∑ i, ∑ a, ∑ j, σ (x i) * J i j * f a j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
private lemma Hf_sub_right' {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y - z) = PI.NormGramAtOrigin.hform σ J x y - PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
private lemma hform_symm_of_involutive_of_hermitian {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (PI.NormGramAtOrigin.hform σ J x y) = PI.NormGramAtOrigin.hform σ J y x := by
  simp only [PI.NormGramAtOrigin.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hJ j i]; ring
private lemma hform_add_smul_self_ne_zero_of_isotropic_pair {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (w y : Fin n → E)
    (hw : PI.NormGramAtOrigin.hform σ J w w = 0) (hy : PI.NormGramAtOrigin.hform σ J y y = 0) (t : E)
    (ht : PI.NormGramAtOrigin.hform σ J w y = t) (ht0 : t ≠ 0) :
    PI.NormGramAtOrigin.hform σ J (w + σ t • y) (w + σ t • y) ≠ 0 := by
  have e1 : PI.NormGramAtOrigin.hform σ J w (w + σ t • y) = σ t * t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hw, ht, zero_add]
  have e2 : PI.NormGramAtOrigin.hform σ J y w = σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w y, ht]
  have e3 : PI.NormGramAtOrigin.hform σ J y (w + σ t • y) = σ t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hy, e2, mul_zero, add_zero]
  have e4 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) w = t * σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w, e1, map_mul, hσ]
  have e5 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) y = t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y, e3, hσ]
  rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, e4, e5]
  have hs : σ t ≠ 0 := by
    intro h
    apply ht0
    rw [← hσ t, h, map_zero]
  have e6 : t * σ t + σ t * t = 2 * (t * σ t) := by ring
  rw [e6]
  exact mul_ne_zero two_ne_zero (mul_ne_zero ht0 hs)
private lemma exists_ne_zero_mulVec_eq_zero_of_lt {E : Type} [Field E] {k n : ℕ} (hk : k < n) (A : Fin k → Fin n → E) :
    ∃ y : Fin n → E, y ≠ 0 ∧ ∀ a, ∑ j, A a j * y j = 0 := by
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (Matrix.det_eq_zero_of_row_eq_zero
      (A := Matrix.of fun (i j : Fin n) => if h : (i : ℕ) < k then A ⟨i, h⟩ j else 0)
      ⟨k, hk⟩ (fun j => by simp))
  refine ⟨y, hy0, fun a => ?_⟩
  have h := congrFun hy ⟨a, lt_trans a.isLt hk⟩
  simpa [Matrix.mulVec, dotProduct] using h
private lemma exists_hform_ne_zero_of_det_ne_zero {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJd : J.det ≠ 0) (y : Fin n → E) (hy : y ≠ 0) :
    ∃ z : Fin n → E, PI.NormGramAtOrigin.hform σ J z y ≠ 0 := by
  have hJy : Matrix.mulVec J y ≠ 0 := fun h => hJd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy, h⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hJy
  refine ⟨Pi.single i 1, ?_⟩
  have e : PI.NormGramAtOrigin.hform σ J (Pi.single i 1) y = Matrix.mulVec J y i := by
    unfold PI.NormGramAtOrigin.hform
    rw [Finset.sum_eq_single i]
    · simp [Matrix.mulVec, dotProduct]
    · intro l _ hl
      simp [Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e]
  exact hi
private lemma hermC_ppos_col_castLE {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin k → Fin n → E)
    (hvo : ∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0)
    (hvd : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0) (z y0 : Fin n → E)
    (hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0) (hz : PI.NormGramAtOrigin.hform σ J z y0 ≠ 0) :
    ∃ p : Fin n → E, (∀ b, PI.NormGramAtOrigin.hform σ J (v b) p = 0) ∧ PI.NormGramAtOrigin.hform σ J p y0 ≠ 0 := by
  refine ⟨z - ∑ a, (PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a,
    fun b => ?_, ?_⟩
  · rw [Hf_sub_right', hform_sum_right', Finset.sum_eq_single b]
    · rw [hform_smul_right_orbital_bounds_conclusion, div_mul_cancel₀ _ (hvd b), sub_self]
    · intro a _ hab
      rw [hform_smul_right_orbital_bounds_conclusion, hvo b a (Ne.symm hab), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y0, Hf_sub_right', hform_sum_right']
    have h0 : ∀ a, PI.NormGramAtOrigin.hform σ J y0
        ((PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a) = 0 := by
      intro a
      rw [hform_smul_right_orbital_bounds_conclusion, ← hform_symm_of_involutive_of_hermitian σ hσ J hJ (v a) y0, hy0W a, map_zero, mul_zero]
    simp only [h0, Finset.sum_const_zero, sub_zero]
    rw [hform_symm_of_involutive_of_hermitian σ hσ J hJ]
    exact hz
private lemma Hf_e_e_eq_ite {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (hJd : J.det ≠ 0) :
    ∀ k, k ≤ n → ∃ v : Fin k → Fin n → E,
      (∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0) ∧
      ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hvo, hvd⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨y0, hy0, hW0⟩ := exists_ne_zero_mulVec_eq_zero_of_lt (Nat.lt_of_succ_le hk) (fun a j => ∑ l, σ (v a l) * J l j)
    have hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0 := by
      intro a
      calc _ = ∑ j, (∑ l, σ (v a l) * J l j) * y0 j := by
            simp only [PI.NormGramAtOrigin.hform, Finset.sum_mul]
            exact Finset.sum_comm
        _ = 0 := hW0 a
    obtain ⟨z, hz⟩ := exists_hform_ne_zero_of_det_ne_zero σ J hJd y0 hy0
    obtain ⟨p, hpW, hp⟩ := hermC_ppos_col_castLE σ hσ J hJ v hvo hvd z y0 hy0W hz
    have key : ∃ y, (∀ a, PI.NormGramAtOrigin.hform σ J (v a) y = 0) ∧
        PI.NormGramAtOrigin.hform σ J y y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine hform_add_smul_self_ne_zero_of_isotropic_pair σ hσ J hJ p y0 (hcon p hpW) (hcon y0 hy0W) _ rfl hp (hcon _ fun a => ?_)
      rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hpW a, hy0W a, mul_zero, add_zero]
    obtain ⟨y, hyW, hyy⟩ := key
    refine ⟨Fin.snoc (α := fun _ => Fin n → E) v y, fun a b hab => ?_, fun a => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvo a b fun h => hab (congrArg Fin.castSucc h)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hyW a
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ, hyW b, map_zero]
      · exact absurd rfl hab
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvd a
      · simp only [Fin.snoc_last]
        exact hyy
end

set_option autoImplicit false

theorem _root_.solution : PI.NormGramAtOrigin.Statement := by
  unfold PI.NormGramAtOrigin.Statement
  intro E _ _ _ n r hr J hJ hJd
  have hσ : ∀ a : E, starRingEnd E (starRingEnd E a) = a := fun a => by simp
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    rw [starRingEnd_apply]
    exact hJ i j
  obtain ⟨v, hvo, hvd⟩ := Hf_e_e_eq_ite (starRingEnd E) hσ J hJ' hJd r hr
  refine ⟨v, ?_⟩
  have hg : PI.NormGramAtOrigin.gram (starRingEnd E) J v =
      Matrix.diagonal (fun a => PI.NormGramAtOrigin.hform (starRingEnd E) J (v a) (v a)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [PI.NormGramAtOrigin.gram]
    · simp [PI.NormGramAtOrigin.gram, Matrix.diagonal_apply_ne _ h, hvo a b h]
  rw [hg, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => hvd a
