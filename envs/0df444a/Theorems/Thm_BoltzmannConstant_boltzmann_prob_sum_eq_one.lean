-- Prove2me | Theorems.Thm_BoltzmannConstant_boltzmann_prob_sum_eq_one
-- name    : BoltzmannConstant.boltzmann_prob_sum_eq_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:16:12.707154+00:00
-- url     : https://prove2.me/theorems/fd54fa6a-9d8a-42e8-b52d-b42fdfe48ef4
-- title:
--   Boltzmann factors normalised by $Z$ form a probability distribution
-- statement:
--   A system in equilibrium at temperature $T$ occupies a state $i$ of energy $E_i$ with probability weighted by the Boltzmann factor, $P_i = e^{-E_i/(k_BT)}/Z$, where $Z = \sum_j e^{-E_j/(k_BT)}$ is the partition function. For a nonempty finite set of states at positive temperature, these weights are indeed a probability distribution: $$\sum_{i} P_i = 1.$$ This well-posedness statement is the precondition for every later use of Boltzmann factors.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Role in Boltzmann factors" (probability $P_i$ of occupying state $i$, partition function $Z$)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem boltzmann_prob_sum_eq_one {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (T : ℝ) (hT : 0 < T) (E : ι → ℝ) :
    ∑ i ∈ s, boltzmannProb s T E i = 1 := by sorry

end BoltzmannConstant
