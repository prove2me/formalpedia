-- Prove2me | Theorems.Thm_DiaconisStroock_OddPaths_eq_1_8
-- name    : DiaconisStroock.OddPaths.eq_1_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:05:55.588323+00:00
-- url     : https://prove2.me/theorems/505805ce-4a7a-4cfc-9f2e-dfda9ef1e0ce
-- title:
--   (1.8), p. 40 — ½Σ_{x,y}(φ(x)+φ(y))²Q(x,y) = E(φ²) + ⟨φ, Pφ⟩_π
-- statement:
--   Let $P$ be a transition matrix on a finite set $X$ and $\pi$ a stationary distribution of $P$, and write $Q(x,y)=\pi(x)P(x,y)$. For every function $\varphi:X\to\mathbb R$,
--
--   $$
--   \frac12\sum_{x,y\in X}\big(\varphi(x)+\varphi(y)\big)^2Q(x,y)=E(\varphi^2)+\langle\varphi,P\varphi\rangle_{L^2(\pi)},
--   $$
--
--   where $E(\varphi^2)=\sum_x\varphi(x)^2\pi(x)$ is the expectation under $\pi$, $(P\varphi)(x)=\sum_yP(x,y)\varphi(y)$, and $\langle f,g\rangle_{L^2(\pi)}=\sum_xf(x)g(x)\pi(x)$.
--
--   This identity converts the sum over edges produced by the path argument into the quadratic form $E(\varphi^2)+\langle\varphi,P\varphi\rangle$, which equals $(1+\beta)E(\varphi^2)$ on an eigenfunction with eigenvalue $\beta$.
--
--   **Formalization Note** Only stochasticity of $P$ and stationarity of $\pi$ are assumed; reversibility and irreducibility, standing assumptions of the paper, are not needed for this identity and are omitted, which makes the statement more general.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 40, proof of Proposition 2, (1.8), https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
open MarkovMixing

namespace DiaconisStroock.OddPaths

theorem eq_1_8 {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ φ : V → ℝ, 2⁻¹ * ∑ x, ∑ y, (φ x + φ y) ^ 2 * edgeMeasure P π x y =
      innerPi π φ φ + innerPi π φ (P.mulVec φ) := by sorry

end DiaconisStroock.OddPaths
