-- Prove2me | solution 1 for mme_strassenRank_le_tensorRank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-28T20:35:28.332586+00:00
-- url     : https://prove2.me/submissions/ab474b3e-f78f-4f6d-8d98-dc03e7a21711

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen

open MME PiTensorProduct BigOperators

universe u

variable {K : Type u} [Field K] {d : ℕ} {V : Fin d → Type u}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The witness sets defining `tensorRank` and `strassenRank` coincide: an `r`-term
pure-tensor decomposition of `T` is the same data as a restriction of `T` from the
diagonal unit `I_r`. -/
private theorem rank_set_eq (T : PiTensorProduct K V) :
    {r | ∃ f : Fin r → ∀ i, V i, T = ∑ j, tprod K (f j)}
      = {r | Restrict T (diagTensor K d r)} := by
  ext r
  have hmap : ∀ (f : ∀ i, (Fin r → K) →ₗ[K] V i),
      PiTensorProduct.map f (diagTensor K d r)
        = ∑ j : Fin r, tprod K (fun i => f i (Pi.single j (1 : K))) := by
    intro f
    rw [diagTensor, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [PiTensorProduct.map_tprod]
  constructor
  · -- decomposition ⇒ restriction
    rintro ⟨g, hg⟩
    refine ⟨fun i => ∑ j : Fin r,
      LinearMap.smulRight (LinearMap.proj j : (Fin r → K) →ₗ[K] K) (g j i), ?_⟩
    have hf_eval : ∀ (i : Fin d) (k : Fin r),
        (∑ j : Fin r, LinearMap.smulRight (LinearMap.proj j : (Fin r → K) →ₗ[K] K) (g j i))
          (Pi.single k (1 : K)) = g k i := by
      intro i k
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
        LinearMap.proj_apply]
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
        (fun j _ hjk => by rw [Pi.single_eq_of_ne hjk, zero_smul])]
      simp
    rw [hmap]
    simp_rw [hf_eval]
    exact hg.symm
  · -- restriction ⇒ decomposition
    rintro ⟨f, hf⟩
    exact ⟨fun j i => f i (Pi.single j (1 : K)), by rw [← hf]; exact hmap f⟩

/-- `strassenRank T ≤ tensorRank T` (in fact equality). -/
theorem solution (T : PiTensorProduct K V) : strassenRank T ≤ tensorRank T := by
  have h : tensorRank T = strassenRank T := by
    unfold tensorRank strassenRank
    rw [rank_set_eq]
  exact h.ge
