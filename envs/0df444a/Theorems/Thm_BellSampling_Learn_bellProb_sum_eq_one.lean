-- Prove2me | Theorems.Thm_BellSampling_Learn_bellProb_sum_eq_one
-- name    : BellSampling.Learn.bellProb_sum_eq_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:46.620336+00:00
-- url     : https://prove2.me/theorems/0997997b-89e1-45e3-9974-d9635bd228a0
-- title:
--   Preliminaries, p. 1 — the Bell basis is a basis: Bell-sampling probabilities sum to 1
-- statement:
--   Let $\psi$ be a unit vector of $n$ qubits, $\sum_x|\psi(x)|^2=1$. Then the probabilities of the $4^n$ outcomes of Bell sampling on $|\psi\rangle^{\otimes 2}$ sum to one:
--   $$\sum_{r\in\{0,1\}^{2n}} p_\psi(r)=1.$$
--
--   This is the content of "the Bell basis, i.e. the ordered basis of $\mathbb C^4$": the vectors $|\sigma_r\rangle$ form an orthonormal basis of the $2n$-qubit space, so $p_\psi$ is a probability distribution. It ties the success form of the mission's goal ("succeeds with probability at least $1-2^{-n}$") to the page's failure form ("fails with probability at most $2^{-n}$").
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 1, Preliminaries, "the Bell basis, i.e. the ordered basis of C⁴ which we define by"

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem bellProb_sum_eq_one {n : ℕ} (ψ : QState n) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) :
    ∑ r, bellProb ψ r = 1 := by sorry
end BellSampling.Learn
