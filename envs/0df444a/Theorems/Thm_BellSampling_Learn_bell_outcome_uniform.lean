-- Prove2me | Theorems.Thm_BellSampling_Learn_bell_outcome_uniform
-- name    : BellSampling.Learn.bell_outcome_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:36.808504+00:00
-- url     : https://prove2.me/theorems/9d34cdb3-8ead-44cc-b652-16724324809e
-- title:
--   Learning stabilizer states, p. 2 — the Bell outcome is uniform on {t ⊕ s : t ∈ T}
-- statement:
--   Let $\psi$ be an $n$-qubit stabilizer state with stabilizer set $T=T(\psi)$. Then there is a string $s\in\{0,1\}^{2n}$ such that Bell sampling on $|\psi\rangle^{\otimes2}$ returns each $r$ with probability
--   $$p_\psi(r)=\begin{cases}2^{-n}, & r\oplus s\in T,\\ 0, & r\oplus s\notin T,\end{cases}$$
--   i.e. the outcome is uniformly distributed on the coset $\{t\oplus s: t\in T\}$.
--
--   This is the central fact behind Algorithm 1: differences of Bell outcomes land in $T$ and are uniform there.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, Learning stabilizer states, "By eqn. (1), Bell sampling gives an outcome r which is uniformly distributed on the set {t ⊕ s : t ∈ T} for some s ∈ {0, 1}^{2n}."

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem bell_outcome_uniform {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ s : PStr n, ∀ r : PStr n,
      (r + s ∈ stabSet ψ → bellProb ψ r = 1 / 2 ^ n) ∧
      (r + s ∉ stabSet ψ → bellProb ψ r = 0) := by sorry
end BellSampling.Learn
