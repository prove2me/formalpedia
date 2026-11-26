-- Prove2me | solution 1 for section5_power_estimator_exists
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:38.147+00:00
-- url     : https://prove2.me/submissions/9ac349fd-1993-40af-bb58-d282c1e656a7

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_power_column_estimator
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Reconstruction by an explicitly selected column of an operator. This is the
finite arithmetic step used after powering an accurate rank-one estimate. -/









theorem section5_max_column_exists {n : ℕ} (hn : 1 ≤ n)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ j : Fin n, ∀ i, ‖A (section5_coordinate_ket i)‖ ≤ ‖A (section5_coordinate_ket j)‖ := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => ‖A (section5_coordinate_ket i)‖) hne
  exact ⟨j,fun i => hmax i (Finset.mem_univ _)⟩

end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (k : ℕ)
    (hprec : 400*(n:ℝ)/ε ≤ (2:ℝ)^(k+1)) :
    ∃ j : Fin n, ∀ w : EuclideanSpace ℂ (Fin n), ‖w‖=1 →
      ‖L-rankOne ℂ w w‖ ≤ ε/1000 →
        (L^(k+1)) (section5_coordinate_ket j) ≠ 0 ∧
          ∃ ζ : ℂ, ‖ζ‖=1 ∧
            ‖NormedSpace.normalize ((L^(k+1)) (section5_coordinate_ket j))-ζ • w‖ ≤ ε/24 := by
  obtain ⟨j,hj⟩ := section5_max_column_exists hn (L^(k+1))
  exact ⟨j,fun w hw herror => section5_power_column_estimator hn L hL ε hε hε' k hprec j hj w hw herror⟩
