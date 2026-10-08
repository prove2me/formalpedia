-- Prove2me | Theorems.Thm_DiaconisStroock_VarDist_four_tvDist_sq_le
-- name    : DiaconisStroock.VarDist.four_tvDist_sq_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:36.028101+00:00
-- url     : https://prove2.me/theorems/0d0b233b-b714-48a7-b639-0261fbfc4123
-- title:
--   §1D, proof of Proposition 3, p. 42 — Cauchy–Schwarz bound 4‖Pⁿ(x,·) − π‖²_Var ≤ P^{2n}(x,x)/π(x) − 1
-- statement:
--   Let $X$ be a finite set and $P$ the transition matrix of an irreducible Markov chain on $X$, reversible with respect to its stationary probability distribution $\pi$. For probability distributions $\mu, \pi$ on $X$ the variation distance is
--
--   $$\|\mu-\pi\|_{\mathrm{Var}} = \max_{A\subset X} |\mu(A)-\pi(A)| = \tfrac12 \sum_{x\in X}|\mu(x)-\pi(x)|.$$
--
--   Then for every starting state $x \in X$ and every $n\in\mathbb N$, the distribution $P^n(x,\cdot)$ of the chain after $n$ steps satisfies
--
--   $$
--   4\,\|P^n(x,\cdot)-\pi\|_{\mathrm{Var}}^2 \;\le\; \frac{1}{\pi(x)}\,P^{2n}(x,x) - 1.
--   $$
--
--   This is the first half of the proof of Proposition 3: it bounds the variation distance by an $L^2(1/\pi)$ quantity (a $\chi^2$ distance) and then by a diagonal entry of $P^{2n}$.
--
--   **Formalization Note** $\|\mu-\pi\|_{\mathrm{Var}}$ is `MarkovMixing.tvDist μ π`, defined as the supremum over subsets $A$ of $|\mu(A)-\pi(A)|$, and $P^n(x,\cdot)$ is `rowDist P n x`. The square binds before the factor $4$. Positivity of $\pi$ is not assumed; it follows from irreducibility and stationarity. $n = 0$ is included.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 42 (PDF p. 7), §1D, proof of Proposition 3, the displayed chain 4‖Pⁿ(x, ·) − π(·)‖² = … ≤ … = (1/π(x))P^{2n}(x, x) − 1; ‖·‖_Var defined p. 41 (PDF p. 6)

import Mathlib
import Definitions.Def_mm_mixing
open MarkovMixing

namespace DiaconisStroock.VarDist

/-- The Cauchy–Schwarz step in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds
for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`4‖Pⁿ(x, ·) − π‖²_Var ≤ (1/π(x)) P^{2n}(x, x) − 1` for every state `x` and every `n`. -/
theorem four_tvDist_sq_le {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), 4 * tvDist (rowDist P n x) π ^ 2 ≤ (P ^ (2 * n)) x x / π x - 1 := by sorry

end DiaconisStroock.VarDist
