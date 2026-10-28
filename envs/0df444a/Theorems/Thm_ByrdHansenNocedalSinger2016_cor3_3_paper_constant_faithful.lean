-- Prove2me | Theorems.Thm_ByrdHansenNocedalSinger2016_cor3_3_paper_constant_faithful
-- name    : ByrdHansenNocedalSinger2016.cor3_3_paper_constant_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:54:51.23997+00:00
-- url     : https://prove2.me/theorems/7184a24b-4df8-4881-bdfd-0658f0b75435
-- title:
--   Corollary 3.3 — expected suboptimality Q(β)/k for the SQN method, with the paper's constant (3.24)
-- statement:
--   Let $f_1, \dots, f_N$ be twice continuously differentiable functions on $\mathbb{R}^n$ and let $F = \frac{1}{N} \sum_{i=1}^{N} f_i$ be their average. For a subset $S_H \subseteq \{1, \dots, N\}$ of size $b_H$, write $\nabla^2 F_{S_H}(w) = \frac{1}{b_H} \sum_{i \in S_H} \nabla^2 f_i(w)$ for the subsampled Hessian. Fix a memory size $M \ge 1$, an update period $L \ge 1$, batch sizes $1 \le b, b_H \le N$ and constants $\lambda, \Lambda > 0$ such that $\lambda I \prec \nabla^2 F_{S_H}(w) \prec \Lambda I$ for every point $w$ and every subset $S_H$ of size $b_H$, and let $w^\ast$ be a minimizer of $F$. Let $w^1, w^2, \dots$ be the iterates of the stochastic quasi-Newton method of Algorithm 1, with the limited-memory BFGS matrices $H_t$ of Algorithm 2, where the gradient samples have size $b$ and the Hessian samples have size $b_H$. Then there are constants $0 < \mu_1 \le \mu_2$ such that:
--
--   1. on every run whose correction vectors $s_t$ are all nonzero, every matrix $H$ used by the method satisfies $\mu_1 I \prec H \prec \mu_2 I$;
--   2. for every $\beta > \frac{1}{2 \mu_1 \lambda}$, every $\gamma$ and every starting point $w^1$, if on every sample history the correction vectors are nonzero and the second moment of the sampled gradient is at most $\gamma^2$ at every iterate, that is $\frac{1}{N} \sum_{i=1}^{N} \| \nabla f_i(w^k) \|^2 \le \gamma^2$, then the method with step sizes $\alpha^k = \frac{\beta}{k}$ satisfies, for every $k \ge 1$,
--   $$\mathbb{E}\big[F(w^k) - F(w^\ast)\big] \le \frac{Q(\beta)}{k}, \qquad Q(\beta) = \max\left\{ \frac{\Lambda \mu_2^2 \beta^2 \gamma^2}{2 (2 \mu_1 \lambda \beta - 1)},\ F(w^1) - F(w^\ast) \right\},$$
--   where the expectation is over independent, uniformly random samples.
--
--   This is Corollary 3.3 of Byrd, Hansen, Nocedal and Singer with the paper's own constant (3.24): the expected suboptimality of the stochastic quasi-Newton method decays like $\frac{1}{k}$. The goal result of this mission proves the same bound with a larger constant, which has the additional entry $\Lambda \mu_2^2 \beta^2 \gamma^2$ inside the maximum.
--
--   **Formalization Note.** The expectation is the exact average over all finitely many sample histories. The second-moment bound (3.5) of the paper is required at the iterates, with the random sample uniform over the training set. Requiring nonzero correction vectors excludes only the runs on which Algorithm 2 would divide by zero.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016) 1008-1031, doi:10.1137/140954362, p. 1018, Corollary 3.3, Eqs. (3.23)-(3.24); Assumption 1 and Lemma 3.1, p. 1015

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS
import Definitions.Def_StochQuasiNewton_SQN_Algorithm
import Definitions.Def_StochQuasiNewton_SQN_NewtonLike

open scoped RealInnerProductSpace
open StochQuasiNewton.SQN

theorem ByrdHansenNocedalSinger2016.cor3_3_paper_constant_faithful {n N : ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (M L b bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) (hb : 1 ≤ b) (hbN : b ≤ N) (hbH : 1 ≤ bH)
    (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn (objective f) Set.univ wstar) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ μ₂ ∧
      (∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
        (∀ t, 1 ≤ t → sqnPairS f M L α w1 S SH t ≠ 0) →
        ∀ k, 1 ≤ k →
          (sqnAppliedMatrix f M L α w1 S SH k -
              μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) -
              sqnAppliedMatrix f M L α w1 S SH k).PosDef) ∧
      (∀ (β γ : ℝ) (w1 : EuclideanSpace ℝ (Fin n)), 1 / (2 * μ₁ * lam) < β →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ t, 1 ≤ t → sqnPairS f M L (fun k => β / k) w1 S SH t ≠ 0) →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ k, 1 ≤ k →
            (1 / (N : ℝ)) * ∑ i, ‖gradient (f i) (sqnIterate f M L (fun k => β / k) w1 S SH k)‖ ^ 2
              ≤ γ ^ 2) →
        ∀ k, 1 ≤ k →
          sampleExpectation N b bH k (fun S SH =>
              objective f (sqnIterate f M L (fun k => β / k) w1 S SH k) - objective f wstar) ≤
            max (Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / (2 * (2 * μ₁ * lam * β - 1)))
                (objective f w1 - objective f wstar) / k) := by sorry
