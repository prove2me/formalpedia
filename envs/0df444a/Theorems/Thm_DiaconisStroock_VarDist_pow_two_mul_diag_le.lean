-- Prove2me | Theorems.Thm_DiaconisStroock_VarDist_pow_two_mul_diag_le
-- name    : DiaconisStroock.VarDist.pow_two_mul_diag_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:49.420115+00:00
-- url     : https://prove2.me/theorems/163c60eb-64ae-4e1e-a82c-dd28dd71c654
-- title:
--   §1D, proof of Proposition 3, p. 42 — diagonal bound P^{2n}(x,x) ≤ π(x) + β_*^{2n}(1 − π(x))
-- statement:
--   Let $X$ be a finite set with $m = |X|$ elements and $P$ the transition matrix of an irreducible Markov chain on $X$, reversible with respect to its stationary probability distribution $\pi$. Its eigenvalues are real, $1 = \beta_0 > \beta_1 \ge \dots \ge \beta_{m-1} \ge -1$, and
--
--   $$\beta_* = \max(\beta_1, |\beta_{m-1}|)$$
--
--   is the largest modulus of an eigenvalue other than $\beta_0 = 1$. Then for every state $x\in X$ and every $n\in\mathbb N$,
--
--   $$
--   P^{2n}(x,x) \;\le\; \pi(x) + \beta_*^{2n}\,\bigl(1-\pi(x)\bigr).
--   $$
--
--   In the paper this comes from the spectral expansion $P^{2n}(x,x) = \pi(x) + \sum_{w\ne z} B_{ww}^{2n}\Gamma_{xw}^2$, where the eigenvalue $1$ contributes $\pi(x)$ and the remaining weights $\Gamma_{xw}^2$ sum to $1-\pi(x)$. Combined with the Cauchy–Schwarz bound it gives (1.9).
--
--   **Formalization Note** $\beta_*$ is `MarkovMixing.lambdaStar P`, the supremum of $|\lambda|$ over real eigenvalues $\lambda \ne 1$ of $P$. For an irreducible reversible chain the eigenvalue $1$ is simple and all eigenvalues are real, so this set is $\{|\beta_1|,\dots,|\beta_{m-1}|\}$ and its maximum is $\max(\beta_1,|\beta_{m-1}|)$. When $|X| = 1$ the set is empty and `lambdaStar P = 0`; the inequality then reads $1 \le 1 + 0^{2n}\cdot 0$, still true, so no hypothesis $|X|\ge 2$ is needed. $n = 0$ is included (both sides equal $1$).
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 42 (PDF p. 7), §1D, proof of Proposition 3: "the x, x entry of P^{2n} is π(x) + Σ_{w≠z} B_ww^{2n} Γ_xw². Bounding B_ww^{2n} by β_*^{2n} and using the orthogonality of Γ, the inequality (1.9) of the lemma follows"

import Mathlib
import Definitions.Def_mm_spectral
open MarkovMixing

namespace DiaconisStroock.VarDist

/-- The diagonal bound in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds for
eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`P^{2n}(x, x) ≤ π(x) + β_*^{2n} (1 − π(x))`, where `β_* = lambdaStar P` is the largest modulus of
an eigenvalue different from `1`. -/
theorem pow_two_mul_diag_le {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), (P ^ (2 * n)) x x ≤ π x + lambdaStar P ^ (2 * n) * (1 - π x) := by sorry

end DiaconisStroock.VarDist
