-- Prove2me | Theorems.Thm_FiniteContinuousCommonSubdivision__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
-- name    : FiniteContinuousCommonSubdivision__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T15:22:53.899746+00:00
-- url     : https://prove2.me/theorems/66cd916f-1b28-48b4-8f4e-10b051ad3bf1
-- title:
--   Common finite subdivision for finitely many continuous real functions
-- statement:
--   For any positive tolerance, finitely many continuous real functions on the unit interval share a finite increasing subdivision on which every successive absolute value change is at most that tolerance. Uniform continuity supplies a common positive mesh size. The finite family may be empty.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Mathlib.Topology.Instances.Real.Lemmas

theorem FiniteContinuousCommonSubdivision__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
    {ι : Type} [DecidableEq ι] (f : ι → ℝ → ℝ) (N : Finset ι)
    (hf : ∀ i ∈ N, ContinuousOn (f i) (Set.Icc (0 : ℝ) 1))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : ℕ → ℝ),
      0 < m ∧ t 0 = 0 ∧ t m = 1 ∧
      (∀ k ≤ m, t k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ k < m, t k ≤ t (k + 1)) ∧
      ∀ k < m, ∀ i ∈ N, |f i (t (k + 1)) - f i (t k)| ≤ δ := by
  sorry
