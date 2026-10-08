-- Prove2me | Theorems.Thm_DiaconisStroock_VarDist_proposition_3
-- name    : DiaconisStroock.VarDist.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:08:01.431934+00:00
-- url     : https://prove2.me/theorems/f08f831d-7453-48a1-82bd-a9b19db7b9d2
-- title:
--   Proposition 3, (1.9), pp. 41–42 — 4‖Pⁿ(x,·) − π‖²_Var ≤ ((1 − π(x))/π(x)) β_*^{2n} for reversible chains
-- statement:
--   Let $X$ be a finite set with $m = |X|$ elements and $P(x,y)$ the transition matrix of an irreducible Markov chain on $X$, reversible with respect to its stationary probability distribution $\pi$:
--
--   $$\pi(x)P(x,y) = \pi(y)P(y,x) \qquad (x,y\in X).$$
--
--   The eigenvalues of $P$ are real, $1 = \beta_0 > \beta_1 \ge \dots \ge \beta_{m-1} \ge -1$; put $\beta_* = \max(\beta_1, |\beta_{m-1}|)$. The variation distance between probability distributions $\mu,\pi$ on $X$ is $\|\mu-\pi\|_{\mathrm{Var}} = \max_{A\subset X}|\mu(A)-\pi(A)|$.
--
--   **Proposition 3, (1.9).** For every starting state $x\in X$ and every $n \in \mathbb N$,
--
--   $$
--   4\,\|P^n(x,\cdot)-\pi\|_{\mathrm{Var}}^2 \;\le\; \frac{1-\pi(x)}{\pi(x)}\,\beta_*^{2n}.
--   $$
--
--   This is the basic eigenvalue bound on the distance to stationarity of a reversible chain: once $\beta_*$ is bounded away from $1$ (for instance by the geometric bounds of Propositions 1 and 2 of the same paper), it gives an explicit number of steps after which the chain started at $x$ is close to $\pi$ in variation distance.
--
--   **Formalization Note** The chain is a real matrix `P` with `IsStochastic P`, `MarkovMixing.Irreducible P`, a stationary probability vector `π` (`IsStationary P π`) and detailed balance `DetailedBalance P π`. $\|P^n(x,\cdot)-\pi\|_{\mathrm{Var}}$ is `tvDist (rowDist P n x) π`, and $\beta_*$ is `lambdaStar P`, the supremum of $|\lambda|$ over real eigenvalues $\lambda\ne 1$ of $P$, which equals $\max(\beta_1,|\beta_{m-1}|)$ for an irreducible reversible chain (the eigenvalue $1$ is simple and all eigenvalues are real). Positivity of $\pi$ is not assumed: it follows from irreducibility and stationarity. The case $n = 0$ is included; there the bound reads $4(1-\pi(x))^2 \le (1-\pi(x))/\pi(x)$, which holds because $4\pi(x)(1-\pi(x))\le 1$. On a one-point space both sides are $0$ (the eigenvalue set is empty and `lambdaStar P = 0`), so no hypothesis $|X|\ge 2$ is added.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), pp. 41–42 (PDF pp. 6–7), Proposition 3, (1.9); ‖·‖_Var defined p. 41; standing assumption §1A, (1.1), p. 36

import Mathlib
import Definitions.Def_mm_spectral
open MarkovMixing

namespace DiaconisStroock.VarDist

/-- **Proposition 3, (1.9)** (Diaconis and Stroock, Geometric bounds for eigenvalues of Markov
chains, Ann. Appl. Probab. 1 (1991), pp. 41–42): for an irreducible chain `P` on a finite set,
reversible with respect to its stationary distribution `π`,
`4‖Pⁿ(x, ·) − π‖²_Var ≤ ((1 − π(x))/π(x)) β_*^{2n}` for every state `x` and every `n`, where
`β_* = lambdaStar P = max(β₁, |β_{m−1}|)`. -/
theorem proposition_3 {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ),
      4 * tvDist (rowDist P n x) π ^ 2 ≤ (1 - π x) / π x * lambdaStar P ^ (2 * n) := by sorry

end DiaconisStroock.VarDist
