-- Prove2me | Theorems.Thm_Delmotte_stepProb_le_mul_heatKernel_of_le_diag
-- name    : Delmotte.stepProb_le_mul_heatKernel_of_le_diag
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:32:07.15889+00:00
-- url     : https://prove2.me/theorems/d23251b4-9a90-4dec-85aa-562212000ff9
-- title:
--   Delmotte, Theorem 3.6 (as Erschler–Zheng apply it) — if J(x,x) ≥ α > 0, then Jᵗ(x,y) ≤ C(α)·p(t,x,y) for every integer t ≥ 0
-- statement:
--   For every real $\alpha > 0$ there is a constant $C > 0$, chosen before everything else and so depending only on $\alpha$, with the following property. Let $X$ be a countable set and $J$ a symmetric transition kernel on $X$ (`IsTransition J`, `IsSymmetric J`) with $J(x,x) \ge \alpha$ for every $x$. Then for every integer $t \ge 0$ and all $x, y \in X$,
--   $$J^t(x,y) \le C\,p(t,x,y),$$
--   where $J^t$ is the $t$-step kernel (`stepProb J t`) and $p(t,x,y) = \sum_{n\ge0}e^{-t}\frac{t^n}{n!}J^n(x,y)$ (`heatKernel J t x y`) is the transition function at time $t$ of the continuous-time walk that jumps according to $J$ at rate one. Both sides are taken at the same time $t$ and the same pair $(x,y)$. Since $J(x,x) \le \sum_y J(x,y) = 1$, the hypothesis can hold on a non-empty $X$ only for $\alpha \le 1$.
--
--   T. Delmotte, *Parabolic Harnack inequality and estimates of Markov chains on graphs*, Rev. Mat. Iberoam. 15 (1999) 181–232, [doi:10.4171/RMI/254](https://doi.org/10.4171/RMI/254), sets $p(x,y) = \mu_{xy}/m(x)$ with $m(x) = \sum_{y\sim x}\mu_{xy}$, lets $p_n$ be its $n$-step kernel, and defines (p. 186): “The continuous-time Markov kernel may be defined by $\mathcal P_t(x,z) = e^{-t}\sum_{k=0}^{+\infty}\frac{t^k}{k!}p_k(x,z)$.” In §3.2 Delmotte proves (p. 218): “**Theorem 3.6.** Assume $(\Gamma,\mu)$ satisfies $p(x,x) \ge \alpha > 0$ for all $x$ in $\Gamma$. Then, for all $x, y, n$, $p_n(x,y) \le C(\alpha)\,\mathcal P_n(x,y)$.”
--
--   A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2), write in the proof of Proposition 7.11 (p. 50): “It is elementary and well-known that when $J(x,x) \geqslant \alpha > 0$, the continuous time transition probability and discrete time transition probabilities are comparable, because the former is a Poissonization of the later, see for example [22, Subsection 3.2]. By [22, Theorem 3.6], the discrete time transition probability $P^t_{\mu_\beta}(x,y) \leqslant Cp(t,x,y)$ where $C > 0$ is a constant that only depends on $\mu_\beta(id)$.”
--
--   With $\mu_{xy} = J(x,y)$, the weights are $m(x) = \sum_y J(x,y) = 1$, so $p = J$ and $p_n = J^n$, and $\mathcal P_t$ is the series `heatKernel J t` (the deficit $1 - \sum_z J(x,z)$ that `uniformize` adds on the diagonal is $0$); this statement is Theorem 3.6 for such weights. The constant is chosen from $\alpha$ alone, matching Erschler and Zheng’s “only depends on $\mu_\beta(id)$”, where $\mu_\beta(id)$ plays the role of $\alpha$.
--
--   Delmotte’s standing assumptions (§1.1, p. 183) are more restrictive than this statement’s hypotheses: “Let $\Gamma$ be an infinite set and $\mu_{xy} = \mu_{yx} \ge 0$ a symmetric weight on $\Gamma\times\Gamma$. … We will assume that this graph is connected and locally uniformly finite”. Here $X$ may be finite or disconnected, and $J$ need not be locally finite.
--
--   The proof here follows Delmotte’s proof of Theorem 3.6 (pp. 216–218) and uses none of these assumptions. With $q = J - \alpha I$, which has non-negative entries, $J^n = \sum_{k\le n}\binom nk\alpha^{n-k}q^k$, the second expansion in (3.19) (p. 216). Of the first, $\mathcal P_n = e^{(\alpha-1)n}\sum_k\frac{n^k}{k!}q^k$, only the lower bound by its terms with $k \le n$ is used; it comes from expanding each $J^j$ in the heat-kernel series and summing the non-negative terms in the other order. The coefficients compare as $\binom nk\alpha^{n-k} \le K(\alpha)\,e^{(\alpha-1)n}\frac{n^k}{k!}$ for $k \le n$, with $K(\alpha) = 1 + e/\sqrt{3\alpha/20}$: the first assertion of Lemma 3.5 (p. 217), with an explicit constant, proved from Stirling’s bounds for $n!$ and $(n-k)!$. So $C = K(\alpha)$ works. The symmetry of $J$ is assumed, as in Delmotte’s setting; the proof does not use it.
-- source:
--   T. Delmotte, Parabolic Harnack inequality and estimates of Markov chains on graphs, Rev. Mat. Iberoam. 15 (1999) 181–232, https://doi.org/10.4171/RMI/254, Section 3.2, Theorem 3.6, as applied in A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 50 (proof of Proposition 7.11)

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

universe u

open DurrettProbability MarkovChain

namespace Delmotte

theorem stepProb_le_mul_heatKernel_of_le_diag (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J : X → X → ℝ),
      IsTransition J → IsSymmetric J → (∀ x, α ≤ J x x) →
      ∀ (t : ℕ) (x y : X), stepProb J t x y ≤ C * heatKernel J t x y := by
  sorry

end Delmotte
