-- Prove2me | Theorems.Thm_CarlenKusuokaStroock_heatKernel_le_exp_davies
-- name    : CarlenKusuokaStroock.heatKernel_le_exp_davies
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:31:51.257989+00:00
-- url     : https://prove2.me/theorems/3d9c6ef6-bb74-4a12-85e3-af481bb90086
-- title:
--   Carlen–Kusuoka–Stroock, Theorem 3.25 (as Erschler–Zheng apply it in (7.15)) — the Nash inequality for J^R_1 gives the Davies bound on p_R
-- statement:
--   For real numbers $C > 0$ and $\beta > 0$ there is a constant $C_2 > 0$, chosen before everything else and so depending only on $C$ and $\beta$, with the following property. Let $X$ be a countable set, $J$ a symmetric transition kernel on $X$ (`IsTransition J`, `IsSymmetric J`), $\rho$ a metric on $X$ (`IsMetric ρ`), $\phi : \mathbb R \to \mathbb R$ a function and $R$ a real number with $\phi(R) > 0$. Suppose the near part $J^R_1$ of $J$ (`nearPart J ρ R`: $J^R_1(x,y) = J(x,y)$ if $\rho(x,y) \le R$, and $0$ otherwise) satisfies the Nash inequality with constants $C$, $\delta = 4/\phi(R)$ and $\beta$ (`SatisfiesNash (nearPart J ρ R) C (4 / φ R) β`): for every finitely supported $f : X \to \mathbb R$,
--   $$\|f\|_2^{2(1+\beta)} \le C\Bigl(\mathcal E_{J^R_1}(f) + \tfrac{4}{\phi(R)}\|f\|_2^2\Bigr)\|f\|_1^{2\beta},$$
--   with $\|f\|_2^2 = \sum_x f(x)^2$, $\|f\|_1 = \sum_x|f(x)|$ and $\mathcal E_{J^R_1}(f) = \frac12\sum_{x,y}(f(x)-f(y))^2J^R_1(x,y)$. Then for every $\psi : X \to \mathbb R$ with $\Lambda_R(\psi)^2 < \infty$, every real $t > 0$ and all $x, y \in X$,
--   $$p_R(t,x,y) \le C_2\,t^{-1/\beta}\exp\Bigl(\tfrac{4t}{\phi(R)} + 72\,\Lambda_R(\psi)^2\,t - \psi(y) + \psi(x)\Bigr).$$
--   Here $p_R$ is the heat kernel of $J^R_1$ (`heatKernel (nearPart J ρ R)`), the transition function of the jump process with jump kernel $J^R_1$. The quantity $\Lambda_R(\psi)^2$ (`daviesSq (nearPart J ρ R) ψ`, a value in $[0,\infty]$) is the larger of $\sup_x e^{-2\psi(x)}\Gamma(e^\psi)(x)$ and $\sup_x e^{2\psi(x)}\Gamma(e^{-\psi})(x)$, where $\Gamma(g)(x) = \sum_y(g(y)-g(x))^2J^R_1(x,y)$ (`carreDuChamp`) carries no factor $\frac12$. Every $\psi$ with $\Lambda_R(\psi)^2$ finite is allowed, bounded or not. The constant $C_2$ depends neither on $R$ nor on $\phi$, which enters only through the number $\phi(R)$.
--
--   E. A. Carlen, S. Kusuoka and D. W. Stroock, *Upper bounds for symmetric Markov transition functions*, Ann. Inst. H. Poincaré Probab. Statist. 23 (1987), no. 2, suppl., 245–287 (no DOI; [Numdam](https://www.numdam.org/item/AIHPB_1987__23_S2_245_0/)), suppose on p. 269 “that $\mathscr E$ satisfies the Nash inequality (3.18) $\|f\|_2^{2+4/\nu} \leqq A(\mathscr E(f,f) + \delta\|f\|_2^2)\|f\|_1^{4/\nu}$, $f \in L^2(m)$”, and prove on p. 272: “**(3.25) Theorem.** — Assume that (3.18) holds for some positive $\nu$, $A$, and $\delta$. Then $P(t,x,dy) = p(t,x,y)m(dy)$ where, for each $\rho \in (0,1]$ and all $(t,x,y) \in (0,\infty)\times E\times E$: (3.26) $p(t,x,\cdot) \leqq C(A/\rho t)^{\nu/2}e^{\delta\rho t}e^{-D((1+\rho)t;\,x,\,\cdot)}$ ($m$-a.e.) with $C \in (0,\infty)$ depending only on $\nu$ and (3.27) $D(T;x,y) \equiv \sup\{|\psi(y)-\psi(x)| - T\Gamma(\psi)^2 : \psi \in \hat{\mathscr F}_\infty\}$.” Their $\rho$ is a parameter, not a metric.
--
--   A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2), write in the proof of Proposition 7.20 (pp. 51–52): “Then by [15, Theorem 3.25], for any function $\psi$ on $X$, (7.15) $p_R(t,x,y) \leqslant C_2t^{-\frac1\beta}\exp\left(\frac{4t}{\phi(R)} + 72\Lambda_R(\psi)^2t - \psi(y) + \psi(x)\right)$, where $C_2 > 0$ is a constant and the quantity $\Lambda_R(\psi)$ is defined as $\Lambda_R(\psi)^2 = \max\{\|e^{-2\psi}\Gamma(e^\psi,e^\psi)\|_\infty, \|e^{2\psi}\Gamma(e^{-\psi},e^{-\psi})\|_\infty\}$, $\Gamma_R(f,g)(x) = \sum_{y\in X}(f(y)-f(x))(g(y)-g(x))J_1^R(x,y)$.”
--
--   **The class of $\psi$.** Theorem 3.25 takes $\psi$ in $\hat{\mathscr F}_\infty$, defined on p. 266 inside “$\hat{\mathscr F} \equiv \{h + c: h \in \mathscr F_b \cap C_b(E)$ and $c \in \mathbb R^1\}$”, where $\mathscr F_b$ is the set of bounded functions in the domain of $\mathscr E$ (p. 264). This statement allows every $\psi$ with $\Lambda_R(\psi)^2 < \infty$, bounded or not.
--
--   **The formal proof.** The formal proof does not cite Theorem 3.25. It carries out the argument of that proof for $U$ = `uniformize (nearPart J ρ R)`, with $\delta = 4/\phi(R)$, in three parts.
--
--   - *Unbounded $\psi$ reduce to bounded ones.* Both terms in $\Lambda_R(\psi)^2$ are suprema over $x$ of $\sum_y\bigl(e^{\pm(\psi(y)-\psi(x))} - 1\bigr)^2J^R_1(x,y)$. The clamped function $\psi_n = \max(-n, \min(\psi, n))$ moves every difference $\psi(y) - \psi(x)$ towards $0$ without changing its sign, so $\Lambda_R(\psi_n)^2 \le \Lambda_R(\psi)^2$. For $n \ge |\psi(x)|, |\psi(y)|$ the bound for $\psi_n$ at $(x,y)$ then implies the bound for $\psi$.
--   - *An $\ell^2$ bound on columns, for bounded $\psi$.* For $f \ge 0$ finitely supported, let $F_\tau = e^{\psi}P_\tau(e^{-\psi}f)$, where $P_\tau$ is the heat semigroup of $J^R_1$. For $a, b \ge 0$, the discrete Stroock–Varopoulos inequality is $(a^m - b^m)^2 \le m(a - b)(a^{2m-1} - b^{2m-1})$. It bounds the derivative of $\sum_zF_\tau(z)^{2m}$ by $-\mathcal E_{J^R_1}(F_\tau^m) + 4m^2\Lambda_R(\psi)^2\sum_zF_\tau(z)^{2m}$, as in (3.19) and (3.20). The Nash inequality extends by truncation to bounded summable functions. Applied to $F_\tau^{2m}$, it doubles the exponent $2m$ on each time window, by Lemma (3.21). The proof iterates on the windows $[s - \frac s34^{-k}, s - \frac s34^{-k-1}]$, starting from $\ell^2$ on $[0, 2s/3]$, and lets $k \to \infty$. By duality this gives
--   $$\sum_z\bigl(e^{-\psi(z)}p_R(s,z,y)e^{\psi(y)}\bigr)^2 \le 16^{1/\beta}\Bigl(\frac C\beta\Bigr)^{1/\beta}s^{-1/\beta}\,e^{\delta s + \frac{26}{3}\Lambda_R(\psi)^2s} \le 16^{1/\beta}\Bigl(\frac C\beta\Bigr)^{1/\beta}s^{-1/\beta}\,e^{2\delta s + 72\Lambda_R(\psi)^2s}.$$
--   - *The pointwise bound.* $\Lambda_R(-\psi)^2 = \Lambda_R(\psi)^2$. The semigroup law at $s = t/2$, the symmetry of $p_R$ and the Cauchy–Schwarz inequality combine the column bound for $\psi$ at $y$ with the one for $-\psi$ at $x$.
--
--   This gives the statement with $C_2 = 2^{1/\beta}\,16^{1/\beta}(C/\beta)^{1/\beta}$, and with $36\,\Lambda_R(\psi)^2t$ in place of $72\,\Lambda_R(\psi)^2t$.
-- source:
--   E. A. Carlen, S. Kusuoka and D. W. Stroock, Upper bounds for symmetric Markov transition functions, Ann. Inst. H. Poincaré Probab. Statist. 23 (1987), no. 2, suppl., 245–287 (no DOI; http://www.numdam.org/item/AIHPB_1987__23_S2_245_0/), Theorem 3.25, as applied in A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 51, (7.15)

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

universe u

open DurrettProbability MarkovChain

namespace CarlenKusuokaStroock

theorem heatKernel_le_exp_davies (C β : ℝ) (hC : 0 < C) (hβ : 0 < β) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J ρ : X → X → ℝ)
      (φ : ℝ → ℝ) (R : ℝ),
      IsTransition J → IsSymmetric J → IsMetric ρ → 0 < φ R →
      SatisfiesNash (nearPart J ρ R) C (4 / φ R) β →
      ∀ ψ : X → ℝ, daviesSq (nearPart J ρ R) ψ ≠ ⊤ → ∀ t : ℝ, 0 < t → ∀ x y,
        heatKernel (nearPart J ρ R) t x y ≤
          C₂ * t ^ (-1 / β) *
            Real.exp (4 * t / φ R + 72 * (daviesSq (nearPart J ρ R) ψ).toReal * t - ψ y + ψ x) := by
  sorry

end CarlenKusuokaStroock
