-- Prove2me | Theorems.Thm_DiaconisStroock_VarDist_pow_two_mul_diag_div_eq
-- name    : DiaconisStroock.VarDist.pow_two_mul_diag_div_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:27.839835+00:00
-- url     : https://prove2.me/theorems/a1226a2c-315f-49c9-91b9-631aac756830
-- title:
--   §1D, proof of Proposition 3, p. 42 — reversibility identity P^{2n}(x,x)/π(x) = Σ_y Pⁿ(x,y)²/π(y)
-- statement:
--   Let $X$ be a finite set and $P$ the transition matrix of an irreducible Markov chain on $X$, reversible with respect to its stationary probability distribution $\pi$: $\pi(x)P(x,y) = \pi(y)P(y,x)$ for all $x, y \in X$. Write $P^n(x,y)$ for the $n$-step transition probabilities. Then for every state $x \in X$ and every $n \in \mathbb N$,
--
--   $$
--   \frac{1}{\pi(x)}\,P^{2n}(x,x) \;=\; \sum_{y\in X} \frac{\bigl(P^n(x,y)\bigr)^2}{\pi(y)}.
--   $$
--
--   This identity turns the $\chi^2$-type sum produced by the Cauchy–Schwarz step in the proof of Proposition 3 into a single diagonal entry of $P^{2n}$, which can then be controlled spectrally.
--
--   **Formalization Note** The chain is a real matrix `P` with `IsStochastic P`, irreducibility is `MarkovMixing.Irreducible P` (every state reaches every state), `IsStationary P π` says $\pi$ is a probability vector with $\pi P = \pi$, and `DetailedBalance P π` is reversibility. Irreducibility and stationarity together give $\pi(x) > 0$ for all $x$ ("π charges every point", §1A), so the divisions are by positive numbers; no positivity hypothesis is added. The case $n = 0$ is included (both sides equal $1/\pi(x)$).
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 42 (PDF p. 7), §1D, proof of Proposition 3: "the identity 1/(π(x))P^{2n}(x, x) = Σ_y (Pⁿ(x, y))²/π(y) follows from reversibility"; standing assumption §1A, (1.1), p. 36

import Mathlib
import Definitions.Def_mm_basic
open MarkovMixing

namespace DiaconisStroock.VarDist

/-- The reversibility identity in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds
for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`(1/π(x)) P^{2n}(x, x) = ∑_y (Pⁿ(x, y))² / π(y)` for every state `x` and every `n`. -/
theorem pow_two_mul_diag_div_eq {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), (P ^ (2 * n)) x x / π x = ∑ y, ((P ^ n) x y) ^ 2 / π y := by sorry

end DiaconisStroock.VarDist
