-- Prove2me | Theorems.Thm_Coulhon_stepProb_le_and_heatKernel_le_of_isoperimetricProfile_ge
-- name    : Coulhon.stepProb_le_and_heatKernel_le_of_isoperimetricProfile_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:31:40.602508+00:00
-- url     : https://prove2.me/theorems/2fd75f65-f200-4ba7-b6c0-228cb2ef1e90
-- title:
--   Coulhon, Proposition II.1 (as Erschler–Zheng apply it) — Λ(v) ≥ c·v^(−β) for v ≥ 1 gives Pᵗ(x,y) ≤ C·t^(−1/β) and p(t,x,y) ≤ C·t^(−1/β)
-- statement:
--   For real numbers $c > 0$ and $\beta > 0$ there is a constant $C > 0$, chosen before everything else and so depending only on $c$ and $\beta$, with the following property. Let $X$ be a countable set and $P$ a symmetric transition kernel on $X$ (`IsTransition P`, `IsSymmetric P`) whose $\ell^2$-isoperimetric profile for the counting measure satisfies $\Lambda_P(v) \ge c\,v^{-\beta}$ for every real $v \ge 1$. Here $\Lambda_P(v)$ (`isoperimetricProfile P (fun _ => 1) v`) is the infimum of the Dirichlet eigenvalues $\lambda_1(\Omega)$ over the non-empty finite sets $\Omega \subseteq X$ with at most $v$ points, and $\lambda_1(\Omega)$ is the infimum of $\frac12\sum_{x,y}(f(x)-f(y))^2P(x,y)$ over the real functions $f$ that vanish outside $\Omega$ and have $\sum_x f(x)^2 = 1$. Then for all $x, y \in X$:
--
--   - $P^t(x,y) \le C/t^{1/\beta}$ for every integer $t \ge 1$, where $P^t$ is the $t$-step kernel (`stepProb P t`);
--   - $p(t,x,y) \le C/t^{1/\beta}$ for every real $t > 0$, where $p(t,x,y) = \sum_{n\ge0}e^{-t}\frac{t^n}{n!}P^n(x,y)$ (`heatKernel P t x y`) is the transition function of the continuous-time walk that jumps according to $P$ at rate one.
--
--   No laziness ($P(x,x) > 0$) and no bounded range are assumed. The time $t = 0$, where $P^0(x,x) = 1$, is excluded; the paper’s $\mathbb N$ starts at $1$ (p. 51 sums over “$t \in \{0\}\cup\mathbb N$”).
--
--   T. Coulhon, *Ultracontractivity and Nash type inequalities*, J. Funct. Anal. 141 (1996) 510–539, [doi:10.1006/jfan.1996.0140](https://doi.org/10.1006/jfan.1996.0140), working on a σ-finite measure space $(X, \xi)$, states on p. 512: “**II.1. Proposition.** Let $T_t$ be a semigroup on $L^p$, $1 \leqslant p \leqslant +\infty$, with infinitesimal generator $-A$. Suppose that $T_t$ is equicontinuous on $L^1$ and $L^\infty$, i.e., $\sup_t\|T_t\|_{1\to1}, \sup_t\|T_t\|_{\infty\to\infty} \leqslant M < +\infty$, and that $\theta(\|f\|_2^2) \leqslant \mathrm{Re}(Af,f)$, $\forall f \in \mathscr D(A)$, $\|f\|_1 \leqslant M$, where $\theta\colon ]0,+\infty[ \to ]0,+\infty[$ is continuous and satisfies $\int^{+\infty}dx/\theta(x) < +\infty$. Then $T_t$ is ultracontractive and $\|T_t\|_{1\to\infty} \leqslant m(t)$, $\forall t > 0$, where $m$ is the solution of $-m'(t) = \theta(m(t))$ on $]0,+\infty[$ such that $m(0) = +\infty$, or alternatively the inverse function of $p(t) = \int_t^{+\infty}dx/\theta(x)$.”
--
--   A. Grigor’yan, *Heat kernel upper bounds on a complete non-compact manifold*, Rev. Mat. Iberoam. 10 (1994) 395–452, [doi:10.4171/RMI/157](https://doi.org/10.4171/RMI/157), proves on a complete non-compact Riemannian manifold $M$ (p. 400): “**Theorem 1.1.** Consider the following hypotheses, 1. $\Lambda$-isoperimetric inequality holds on $M$, i.e. for any pre-compact region $\Omega \subset M$ we have $\lambda_1(\Omega) \ge \Lambda(|\Omega|)$. … 3. For all $x \in M$, and $t > 0$ $p(x,x,t) \le \frac{C}{V(ct)}$. … We claim that $1 \Longrightarrow 2 \Longrightarrow 3 \Longrightarrow 4$”, where $V$ is defined by “(1.11) $t = \int_0^{V(t)}\frac{dv}{v\Lambda(v)}$.”
--
--   A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2), state Proposition 7.19 (p. 48): “Let $P_{\mu_\beta}$ be the transition kernel on $1^\infty\cdot G_\omega$ induced by $\mu_\beta$. Then there exists a constant $C = C(\beta) < \infty$ such that for $t \in \mathbb N$, $\sup_{x,y\in1^\infty\cdot G}P^t_{\mu_\beta}(x,y) \leqslant \frac{C}{t^{1/\beta}}$.” Its proof ends (pp. 48–49): “we have that the $\ell^2$-isoperimetric profile of $P_{\mu_\beta}$ satisfies $\Lambda_{P_{\mu_\beta}}(2^{n-1}) \geqslant \frac{C_\beta}{2}2^{-n\beta},\ n \geqslant 1$. That is, $\Lambda_{P_{\mu_\beta}}(v) \geqslant c_\beta v^{-\beta}$ for $v \geqslant 1$. Such a lower bound for the $\ell^2$-isoperimetric profile implies the stated upper bound, see [17, Proposition II.1] or [34, Theorem 1.1].” They use the continuous-time bound on p. 50: “By Proposition 7.19, the lower bound on $\ell^2$-isoperimetric profile of $J$ implies $\sup_{x,y\in X}p(t,x,y) \leqslant \frac{C}{t^{1/\beta}}$.”
--
--   The formal proof follows Coulhon’s route as far as a Nash inequality, and then replaces Proposition II.1 by a discrete argument.
--
--   1. Every non-empty finite $\Omega$ has $|\Omega| \ge 1$, so the hypothesis gives the Faber–Krahn inequality $\lambda_1(\Omega) \ge c\,|\Omega|^{-\beta}$.
--   2. Faber–Krahn gives the Nash-type inequality $\theta(\|f\|_2^2) \le \mathcal E_P(f)$ for $f \ge 0$ with $\|f\|_1 = 1$, where $\theta(x) = \kappa x^{1+\beta}$ and $\kappa = c\,2^{-1-2\beta}$. For $s > 0$ the function $(f-s)_+$ is supported in a set of at most $1/s$ points, whose Dirichlet eigenvalue is therefore at least $c\,s^\beta$; together with $\mathcal E_P((f-s)_+) \le \mathcal E_P(f)$ and $f^2 \le (f-s)_+^2 + 2sf$ this gives $\mathcal E_P(f) \ge c\,s^\beta(\|f\|_2^2 - 2s)$, and $s = \|f\|_2^2/4$ gives $\theta$. This is Coulhon’s “Application” (p. 517), and the truncation (2.10) in the proof of Grigor’yan’s Lemma 2.1 (p. 408).
--   3. In place of Proposition II.1, the proof applies the Nash inequality to the lazy kernel $W = (I + P)/2$. Let $g_n = W^n\delta_x$ and let $m_k = W^k(x,x)$ be the return probabilities. Then $m_{2n} = \|g_n\|_2^2$, $\|g_n\|_1 = 1$ and $m_{2n} - m_{2n+1} = \frac12\mathcal E_P(g_n)$. The $\ell^2$ contraction of $P$ makes $k \mapsto m_k$ non-increasing. So $\kappa\,m_{2n}^{1+\beta} \le 2(m_{2n} - m_{2n+2})$, and this discrete differential inequality gives $m_{2n} \le (\beta\kappa n/2)^{-1/\beta}$ for $n \ge 1$.
--   4. Since $e^{t(P-I)} = e^{2t(W-I)}$, $p(t,x,x) = \sum_k e^{-2t}\frac{(2t)^k}{k!}\,m_k$. For $t \ge 4$, the terms with $k < t$ have total weight at most $e^{-3t/10}$, and the others are at most $m_{2\lfloor t/2\rfloor}$; for $t < 4$, $p \le 1$. This gives $p(t,x,x) \le C_d\,t^{-1/\beta}$ with
--   $$C_d = \max\Bigl(4^{1/\beta},\ \Bigl(\frac{\beta\kappa}{8}\Bigr)^{-1/\beta} + 1 + q!\,(10/3)^q\Bigr), \qquad q = \lceil 1/\beta\rceil .$$
--   Off the diagonal, $p(t,x,y) \le \frac12\bigl(p(t,x,x) + p(t,y,y)\bigr)$ by the semigroup law at $t/2$.
--
--   The discrete-time bound is in neither cited result, both of which are about continuous time. Coulhon’s discrete-time Proposition V.1 (p. 528) assumes an admissible kernel: one that is lazy and of bounded range on a uniformly locally finite graph (p. 527). Erschler and Zheng’s kernel $P_{\mu_\beta}$ has infinite range, and their Proposition 7.19 is a discrete-time statement.
--
--   The formal proof derives the discrete bound from the continuous one without laziness and without the spectral theorem.
--
--   - The even return probabilities $a_j = P^{2j}(x,x) = \|P^j\delta_x\|_2^2$ are non-increasing, by the $\ell^2$ contraction of $P$. They are log-convex, $a_{j+1}^2 \le a_ja_{j+2}$, by the Cauchy–Schwarz inequality. So if $a_n > 0$, the ratio $r = a_n/a_{n-1}$ satisfies $a_nr^j \le a_jr^n$ for all $j$. Keeping the even terms of the heat series,
--   $$p(2n,x,x) \ge \sum_j e^{-2n}\frac{(2n)^{2j}}{(2j)!}\,a_j \ge a_nr^{-n}e^{-2n}\cosh(2n\sqrt r) \ge \tfrac12\,a_n .$$
--   - $P^{2n}(x,y) \le \frac12\bigl(P^{2n}(x,x) + P^{2n}(y,y)\bigr)$, by Chapman–Kolmogorov, symmetry and $ab \le \frac12(a^2 + b^2)$.
--   - $P^{2n+1}(x,y) \le \sup_z P^{2n}(z,y)$, where $2n + 1 \le \frac32\cdot 2n$, and $P^1 \le 1$.
--
--   This gives both bounds with $C = 2(3/2)^{1/\beta}C_d$.
-- source:
--   T. Coulhon, Ultracontractivity and Nash type inequalities, J. Funct. Anal. 141 (1996) 510–539, https://doi.org/10.1006/jfan.1996.0140, Proposition II.1 (with the Faber–Krahn to Nash step, p. 517), cf. A. Grigor'yan, Heat kernel upper bounds on a complete non-compact manifold, Rev. Mat. Iberoam. 10 (1994) 395–452, https://doi.org/10.4171/RMI/157, Theorem 1.1 (the manifold analogue), as applied in A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 49 (proof of Proposition 7.19) and p. 50 (continuous time); the discrete-time bound is compared with the continuous one by a spectral argument

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

universe u

open DurrettProbability MarkovChain

namespace Coulhon

theorem stepProb_le_and_heatKernel_le_of_isoperimetricProfile_ge (c β : ℝ) (hc : 0 < c)
    (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (P : X → X → ℝ),
      IsTransition P → IsSymmetric P →
      (∀ v : ℝ, 1 ≤ v → c * v ^ (-β) ≤ isoperimetricProfile P (fun _ => 1) v) →
      (∀ t : ℕ, 1 ≤ t → ∀ x y, stepProb P t x y ≤ C / (t : ℝ) ^ (1 / β)) ∧
        ∀ t : ℝ, 0 < t → ∀ x y, heatKernel P t x y ≤ C / t ^ (1 / β) := by
  sorry

end Coulhon
