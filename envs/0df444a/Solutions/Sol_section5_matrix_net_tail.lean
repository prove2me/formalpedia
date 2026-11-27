-- Prove2me | solution 1 for section5_matrix_net_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T22:16:41.529469+00:00
-- url     : https://prove2.me/submissions/a0be8d73-6968-4aad-bc05-09135b40bb3c

import Theorems.Thm_section5_quadratic_form_on_net

set_option autoImplicit false
open MeasureTheory HighDimProb.RandomMatrices

/-- Finite-net union bound for the operator norm of a random rectangular matrix. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {m n : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (M : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (↑N) (1/4))
    (hM : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (↑M) (1/4))
    (t δ : ℝ)
    (htail : ∀ x ∈ N, ∀ y ∈ M,
      μ.real {ω | t < inner ℝ (Matrix.toEuclideanLin (A ω) x) y} ≤ δ) :
    μ.real {ω | 2*t < matrixOpNorm (A ω)} ≤ (N.card : ℝ)*(M.card : ℝ)*δ := by
  classical
  have hNne : (↑N : Set (EuclideanSpace ℝ (Fin n))).Nonempty := by
    obtain ⟨x, hx, _⟩ := hN.2 (EuclideanSpace.single ⟨0,hn⟩ 1) (by simp)
    exact ⟨x,hx⟩
  have hMne : (↑M : Set (EuclideanSpace ℝ (Fin m))).Nonempty := by
    obtain ⟨y, hy, _⟩ := hM.2 (EuclideanSpace.single ⟨0,hm⟩ 1) (by simp)
    exact ⟨y,hy⟩
  have contain : {ω | 2*t < matrixOpNorm (A ω)} ⊆
      ⋃ z ∈ N ×ˢ M, {ω | t < inner ℝ (Matrix.toEuclideanLin (A ω) z.1) z.2} := by
    intro ω hω
    by_contra h
    have hb : ∀ x ∈ N, ∀ y ∈ M,
        inner ℝ (Matrix.toEuclideanLin (A ω) x) y ≤ t := by
      intro x hx y hy
      by_contra hxy
      exact h (by simp only [Set.mem_iUnion, Set.mem_setOf_eq];
                  exact ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,lt_of_not_ge hxy⟩)
    have hs : sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin (A ω) x) y)
        (↑N) (↑M)) ≤ t := by
      apply csSup_le (hNne.image2 hMne)
      rintro z ⟨x,hx,y,hy,rfl⟩
      exact hb x hx y hy
    have bound := (section5_quadratic_form_on_net hn hm (A ω) (1/4)
      (by norm_num) (by norm_num) (↑N) hN (↑M) hM).2
    norm_num at bound
    change 2*t < matrixOpNorm (A ω) at hω
    linarith
  calc
    μ.real {ω | 2*t < matrixOpNorm (A ω)} ≤
        μ.real (⋃ z ∈ N ×ˢ M, {ω | t < inner ℝ (Matrix.toEuclideanLin (A ω) z.1) z.2}) :=
      measureReal_mono contain (measure_ne_top μ _)
    _ ≤ ∑ z ∈ N ×ˢ M, μ.real {ω | t < inner ℝ (Matrix.toEuclideanLin (A ω) z.1) z.2} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ N ×ˢ M, δ := by
      apply Finset.sum_le_sum
      intro z hz
      exact htail z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2
    _ = (N.card : ℝ)*(M.card : ℝ)*δ := by simp
