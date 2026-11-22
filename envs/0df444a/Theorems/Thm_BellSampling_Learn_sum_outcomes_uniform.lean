-- Prove2me | Theorems.Thm_BellSampling_Learn_sum_outcomes_uniform
-- name    : BellSampling.Learn.sum_outcomes_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:46.476173+00:00
-- url     : https://prove2.me/theorems/0bc6e053-094d-4476-a94a-c035b94b6427
-- title:
--   Learning stabilizer states, p. 2 — for two independent outcomes, r₁ ⊕ r₂ is uniform on T
-- statement:
--   Let $\psi$ be an $n$-qubit stabilizer state with stabilizer set $T=T(\psi)$, and let $r_1,r_2$ be two independent outcomes of Bell sampling on $|\psi\rangle^{\otimes 2}$. Then for every $t\in\{0,1\}^{2n}$,
--   $$\Pr[r_1\oplus r_2=t]=\sum_{r_1\oplus r_2=t}p_\psi(r_1)\,p_\psi(r_2)=\begin{cases}2^{-n}, & t\in T,\\ 0,& t\notin T.\end{cases}$$
--
--   So the sum of two outcomes is a uniformly random element of $T$, which is how Algorithm 1 samples $T$.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, Learning stabilizer states, "Thus, for any two such outcomes r1, r2, the sum r1 ⊕ r2 is uniformly distributed in T."

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem sum_outcomes_uniform {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ)
    (t : PStr n) :
    (t ∈ stabSet ψ →
      ∑ r₁, ∑ r₂, (if r₁ + r₂ = t then bellProb ψ r₁ * bellProb ψ r₂ else 0) = 1 / 2 ^ n) ∧
    (t ∉ stabSet ψ →
      ∑ r₁, ∑ r₂, (if r₁ + r₂ = t then bellProb ψ r₁ * bellProb ψ r₂ else 0) = 0) := by sorry
end BellSampling.Learn
