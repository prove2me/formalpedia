-- Prove2me | Theorems.Thm_BellSampling_Learn_eq_1
-- name    : BellSampling.Learn.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:54.275744+00:00
-- url     : https://prove2.me/theorems/2e72981a-215a-42ed-b860-c590bba16ca7
-- title:
--   Eqn (1), p. 2 — the Bell outcome probability equals |⟨ψ|σ_rσ₁₀^{⊗S}|ψ⟩|²/2ⁿ
-- statement:
--   Let $\psi$ be an $n$-qubit vector, $S\subseteq[n]$ and $c\in\mathbb C$ with $|c|=1$, and suppose $|\psi^*\rangle=c\,\sigma_{10}^{\otimes S}|\psi\rangle$. Then for every $r\in\{0,1\}^{2n}$, Bell sampling on $|\psi\rangle^{\otimes2}$ returns $r$ with probability
--   $$p_\psi(r)=\frac{|\langle\psi|\sigma_r\,\sigma_{10}^{\otimes S}|\psi\rangle|^2}{2^n}.$$
--
--   This is eqn (1) of the paper: combined with the stabilizer structure, it shows that the outcome distribution is uniform on a coset of $T(\psi)$.
--
--   **Formalization Note** The subset $S$ and the phase $c$ are hypotheses, the output of the previous milestone ($|\psi^*\rangle=\sigma_{10}^{\otimes S}|\psi\rangle$ up to phase), so that this item is exactly the substitution step of the page.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, eqn (1)

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem eq_1 {n : ℕ} (ψ : QState n) (S : Finset (Fin n)) (c : ℂ) (hc : ‖c‖ = 1)
    (hconj : (fun x => star (ψ x)) = c • (sigma (zStr S)).mulVec ψ) (r : PStr n) :
    bellProb ψ r = ‖∑ x, star (ψ x) * ((sigma r * sigma (zStr S)).mulVec ψ) x‖ ^ 2 / 2 ^ n := by sorry
end BellSampling.Learn
