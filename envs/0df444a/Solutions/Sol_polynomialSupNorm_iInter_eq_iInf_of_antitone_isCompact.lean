-- Prove2me | solution 1 for polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:44.814666+00:00
-- url     : https://prove2.me/submissions/f9dd6bc1-17a5-4f4c-8ec7-9de6b1ae6e4f

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Theorems.Thm_polynomialSupNorm_mono_of_isCompact
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_nonneg

section
open Filter Polynomial Set
private theorem polynomialSupNorm_eq_of_isMaxOn
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) {z : ℂ}
    (hz : z ∈ K) (hmax : IsMaxOn (fun w ↦ ‖p.eval w‖) K z) :
    polynomialSupNorm p K = ‖p.eval z‖ := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun w ↦ ?_) (norm_nonneg _)
    exact Real.iSup_le (fun hw ↦ hmax hw) (norm_nonneg _)
  · exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz
end

set_option autoImplicit false
open Filter Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) (K : ℕ → Set ℂ)
    (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty) :
    polynomialSupNorm p (⋂ n, K n) =
      ⨅ n, polynomialSupNorm p (K n) := by
  let M : ℕ → ℝ := fun n ↦ polynomialSupNorm p (K n)
  have hMbdd : BddBelow (Set.range M) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact polynomialSupNorm_nonneg p (K n)
  have hKclosed : ∀ n, IsClosed (K n) := fun n ↦ (hcompact n).isClosed
  have hI_compact : IsCompact (⋂ n, K n) :=
    (hcompact 0).of_isClosed_subset (isClosed_iInter hKclosed) (iInter_subset K 0)
  apply le_antisymm
  · exact le_ciInf fun n ↦
      polynomialSupNorm_mono_of_isCompact p (iInter_subset K n)
        (hcompact n)
  · by_contra! hlt
    let r : ℝ := (polynomialSupNorm p (⋂ n, K n) + ⨅ n, M n) / 2
    have hIr : polynomialSupNorm p (⋂ n, K n) < r := by
      dsimp only [r]
      linarith
    have hrInf : r < ⨅ n, M n := by
      dsimp only [r]
      linarith
    let L : ℕ → Set ℂ := fun n ↦ K n ∩ {z | r ≤ ‖p.eval z‖}
    have hLclosed : ∀ n, IsClosed (L n) := fun n ↦ by
      exact (hcompact n).isClosed.inter (isClosed_le continuous_const p.continuous.norm)
    have hLcompact : ∀ n, IsCompact (L n) := fun n ↦
      (hcompact n).inter_right (isClosed_le continuous_const p.continuous.norm)
    have hLanti : Antitone L := by
      intro m n hmn z hz
      exact ⟨hanti hmn hz.1, hz.2⟩
    have hLnonempty : ∀ n, (L n).Nonempty := by
      intro n
      obtain ⟨z, hz, hmax⟩ :=
        (hcompact n).exists_isMaxOn (hnonempty n) p.continuous.norm.continuousOn
      refine ⟨z, hz, ?_⟩
      change r ≤ ‖p.eval z‖
      rw [← polynomialSupNorm_eq_of_isMaxOn p (hcompact n) hz hmax]
      simpa only [M] using (hrInf.trans_le (ciInf_le hMbdd n)).le
    obtain ⟨z, hz⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed L
        (fun n ↦ hLanti (Nat.le_succ n)) hLnonempty (hLcompact 0) hLclosed
    have hzI : z ∈ ⋂ n, K n := by
      rw [mem_iInter]
      intro n
      exact (mem_iInter.mp hz n).1
    have hrz : r ≤ ‖p.eval z‖ := (mem_iInter.mp hz 0).2
    have hzM : ‖p.eval z‖ ≤ polynomialSupNorm p (⋂ n, K n) :=
      norm_eval_le_polynomialSupNorm p
        (bddAbove_norm_eval_image_of_isCompact p hI_compact) hzI
    exact (hIr.trans_le (hrz.trans hzM)).false
