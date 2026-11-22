-- Prove2me | Theorems.Thm_BellSampling_Learn_lemma_2
-- name    : BellSampling.Learn.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:00.119464+00:00
-- url     : https://prove2.me/theorems/64e2a018-9b8a-4a77-9071-81f962a76fe9
-- title:
--   Lemma 2, p. 2 — Bell sampling on |ψ⟩^{⊗2} returns r with probability |⟨ψ|σ_r|ψ*⟩|²/2ⁿ
-- statement:
--   Let $\psi\in\mathbb C^{\{0,1\}^n}$ and let $\psi^*$ be its complex conjugate in the computational basis. Bell sampling on $|\psi\rangle^{\otimes2}$ returns the string $r\in\{0,1\}^{2n}$ with probability
--   $$p_\psi(r)=\frac{|\langle\psi|\sigma_r|\psi^*\rangle|^2}{2^n},\qquad \langle\psi|\sigma_r|\psi^*\rangle=\sum_{x,y}\overline{\psi(x)}\,\sigma_r(x,y)\,\overline{\psi(y)}.$$
--
--   This expresses the outcome law of Bell sampling through a single matrix element of $\sigma_r$, which is what makes the outcome distribution of a stabilizer state computable.
--
--   **Formalization Note** The page states the lemma for a state; the identity is homogeneous of degree 4 in $\psi$ on both sides, and is stated here for every vector $\psi$, with no norm hypothesis.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, Lemma 2

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem lemma_2 {n : ℕ} (ψ : QState n) (r : PStr n) :
    bellProb ψ r = ‖∑ x, ∑ y, star (ψ x) * sigma r x y * star (ψ y)‖ ^ 2 / 2 ^ n := by sorry
end BellSampling.Learn
