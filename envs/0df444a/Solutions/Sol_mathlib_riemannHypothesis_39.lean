-- Prove2me | solution 39 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:54.042586+00:00
-- url     : https://prove2.me/submissions/22845286-e6bf-4235-b65b-f52c9079a8f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_verified_square_prime_energy_prefix
import Theorems.Thm_MasulloRH_prime_energy_growth_detects_zero_abscissa
import Theorems.Thm_MasulloRH_sparse_subpower_square_prime_energy
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy

-- Step 1: `MasulloRH.sparse_subpower_square_prime_energy` implies `MasulloRH.finite_square_prime_energy_cap` (accepted reduction of `MasulloRH.finite_square_prime_energy_cap`).
section

set_option autoImplicit false
open Finset ArithmeticFunction MeasureTheory Set
open MasulloRH
theorem MasulloRH.finite_square_prime_energy_cap (N : ℕ) :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    (∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)) ≤ 81 := by
  dsimp only
  by_cases h : N≤10000000
  · exact (verified_square_prime_energy_prefix.2.1 N h).trans (by norm_num)
  · have hRH := prime_energy_growth_detects_zero_abscissa.2.2.mpr sparse_subpower_square_prime_energy
    exact riemannHypothesis_iff_square_sampled_prime_energy.2.1.mp hRH N

end

-- Step 2: `MasulloRH.finite_square_prime_energy_cap` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  by
  obtain ⟨-, h2, -⟩ := MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
  exact h2.mpr (fun N => MasulloRH.finite_square_prime_energy_cap N)

end
