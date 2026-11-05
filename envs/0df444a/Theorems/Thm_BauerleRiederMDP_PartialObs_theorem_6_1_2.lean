-- Prove2me | Theorems.Thm_BauerleRiederMDP_PartialObs_theorem_6_1_2
-- name    : BauerleRiederMDP.PartialObs.theorem_6_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:05:11.095845+00:00
-- url     : https://prove2.me/theorems/89b2f436-d51c-46e0-ab92-846e527d2bd1
-- title:
--   Theorem 6.1.2 — power utility under partial observation, $J_n(x,\rho)=(xS^0_n)^\gamma d_n(\rho)$
-- statement:
--   Consider the terminal wealth problem with partial observation of Section 6.1 (bond with constant rate $i\ge0$, $d$ stocks whose relative risk depends on a hidden Markov chain, Assumption (FM)), with the power utility $U(x)=\frac1\gamma x^\gamma$ on $[0,\infty)$, $0<\gamma<1$. Let $J_n$ be the value functions of the filtered model, $\Phi$ the Bayes operator, $\mu_n$ the filter, $S^0_n=(1+i)^n$ and
--   $$
--   \tilde A=\{\alpha\in\mathbb R^d\mid 1+\alpha\cdot R(y)\ge0\ \text{a.s.}\}.
--   $$
--   Then:
--
--   1. The value functions are $J_n(x,\rho)=(xS^0_n)^\gamma d_n(\rho)$ for $(x,\rho)\in[0,\infty)\times\mathbb P(E_Y)$, where
--   $$
--   d_0\equiv\frac1\gamma,\qquad d_n(\rho)=\sup_{\alpha\in\tilde A}\int\!\!\int d_{n-1}\big(\Phi(\rho,z)\big)\big(1+\alpha\cdot z\big)^\gamma Q^R(dz\mid y)\,\rho(dy).\tag{6.3}
--   $$
--   2. For every $n\ge1$ the supremum in (6.3) is attained by a measurable $\alpha^*_n:\mathbb P(E_Y)\to\tilde A$; for every such choice the optimal amounts invested in the stocks are $f^*_n(x,\rho)=\alpha^*_n(\rho)\,x$, $x\ge0$ (a maximizer of $J_{n-1}$), and the strategy $f_n(h_n):=f^*_{N-n}\big(x_n,\mu_n(\cdot\mid h_n)\big)$ is optimal for the $N$-stage terminal wealth problem (6.2) from every initial wealth $x>0$.
--
--   The optimal investment is a fraction of current wealth that depends on the observations only through the filter.
--
--   Differences from the source:
--   - encoding: $S^0_n$ → $(1+i)^n$; reason: the rate of Section 6.1 is constant, $i_n\equiv i$ (p.61: $S^0_n=(1+i)^n$)
--   - reading: "$\alpha^*_n(\rho)$ is the solution of (6.3)" → a measurable $\alpha^*_n$ with values in $\tilde A$ attaining the supremum in (6.3); its existence is asserted and the optimality statements hold for every such choice; reason: the book presupposes the maximizer exists and does not single one out
--   - encoding: $d_n$ real-valued → $d_n$ with values in $[0,\infty]$; reason: the recursion has nonnegative terms, and finiteness of $d_n$ follows from the formula for $J_n$; no instance changes
--   - encoding: $(\mathcal F^S_n)$-adapted strategies and observable histories $h_n$ → measurable functions of the observed returns $(R_1,\dots,R_n)$; reason: $\mathcal F^S_n=\sigma(R_1,\dots,R_n)$ (Doob–Dynkin), and $h_n$ is a function of $x_0$, the strategy and the returns
--   - encoding: $J_n$, a supremum over $\Pi_N$ (p.158) → supremum over Markov policies of measurable decision rules on $E$ under the law of the return path of the filtered model; reason: the book notes on p.159 (cf. Theorem 2.2.3) that history-dependent policies of the filtered model give the same value
--   - encoding: expectations → extended reals with $\int f=\int f^+-\int f^-$; reason: Lean convention; the positive parts are finite here
--   - encoding: Bayes operator undefined where its normalizing constant is $0$ or $\infty$ → defined as $\rho$ there; reason: a null set of $z$ under the predictive law, so no integral changes
--   - encoding: $E_Y$ a Borel subset of a Polish space → $E_Y$ a standard Borel space; reason: the two classes of measurable spaces coincide up to isomorphism
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 6.1.2, p.178 (PDF 191); setting §6.1, pp.175–177 (PDF 188–190)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_FM61
import Definitions.Def_BauerleRiederMDP_PartialObs_J
import Definitions.Def_BauerleRiederMDP_PartialObs_twValue
import Definitions.Def_BauerleRiederMDP_PartialObs_IsMaximizer
import Definitions.Def_BauerleRiederMDP_PartialObs_markovStrategy
import Definitions.Def_BauerleRiederMDP_PartialObs_dPow

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Theorem 6.1.2** (power utility under partial observation).
Bäuerle & Rieder (2011), Theorem 6.1.2, p.178 (PDF 191): "Let `U` be the power utility with
`0 < γ < 1`. Then it holds:
a) The value functions are given by `J_n(x, ρ) = (x S^0_n)^γ d_n(ρ)`, `(x, ρ) ∈ E_X × IP(E_Y)`, where
the sequence `(d_n)` satisfies the following recursion `d_0 ≡ 1/γ`,
`d_n(ρ) = sup_{α ∈ Ã} ∫ ∫ d_{n−1}(Φ(ρ, z)) (1 + α · z)^γ Q^R(dz|y) ρ(dy)`.  (6.3)
b) The optimal amounts which are invested in the stocks are given by `f*_n(x, ρ) = α*_n(ρ) x`,
`x ≥ 0` where `α*_n(ρ)` is the solution of (6.3). The optimal portfolio strategy is given by
`(f_0, …, f_{N−1})` where `f_n(h_n) := f*_{N−n}(x_n, μ_n(·|h_n))`, `h_n = (x_0, a_0, z_1, x_1, …, x_n)`."
The power utility is `U(x) = (1/γ) x^γ`, `x ∈ [0, ∞)` (p.178), in the setting of §6.1 under
Assumption (FM).

**Formalization Note.** `S^0_n = (1 + i)^n` (constant rate). `d_n` is `dPow` (`ℝ≥0∞`-valued, so
a) also says `d_n(ρ) < ∞` for `x > 0`). "`α*_n(ρ)` is the solution of (6.3)" is read as: `α*_n` is a
measurable function of `ρ` with values in `Ã` attaining the supremum in (6.3); its existence is
stated, and b) is stated for every such choice: `(x, ρ) ↦ α*_n(ρ) x` is a maximizer of `J_{n−1}`,
and the strategy built from `(α*_n)` is optimal for (6.2) from every initial wealth `x > 0`. -/
theorem theorem_6_1_2 {EY : Type*} [MeasurableSpace EY] [StandardBorelSpace EY] {d : ℕ}
    (M : Market EY d) (i : ℝ) (hi : 0 ≤ i) (hFM : FM61 M) (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) :
    (∀ (n : ℕ) (x : ℝ) (ρ : ProbabilityMeasure EY), 0 ≤ x →
      J M i (Set.Ici 0) (fun x => 1 / γ * x ^ γ) n x ρ =
        (((x * (1 + i) ^ n) ^ γ : ℝ) : EReal) * ((dPow M γ n ρ : ℝ≥0∞) : EReal)) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ α : ProbabilityMeasure EY → Fin d → ℝ, Measurable α ∧
      ∀ ρ, α ρ ∈ Atilde M ∧ powObj M γ (dPow M γ (n - 1)) ρ (α ρ) = dPow M γ n ρ) ∧
    (∀ (n : ℕ) (α : ProbabilityMeasure EY → Fin d → ℝ), 1 ≤ n →
      (Measurable α ∧
        ∀ ρ, α ρ ∈ Atilde M ∧ powObj M γ (dPow M γ (n - 1)) ρ (α ρ) = dPow M γ n ρ) →
      IsMaximizer M i (Set.Ici 0) (J M i (Set.Ici 0) (fun x => 1 / γ * x ^ γ) (n - 1))
        (fun p => p.1 • α p.2)) ∧
    (∀ (N : ℕ) (αs : ℕ → ProbabilityMeasure EY → Fin d → ℝ),
      (∀ n : ℕ, 1 ≤ n → n ≤ N → Measurable (αs n) ∧
        ∀ ρ, αs n ρ ∈ Atilde M ∧ powObj M γ (dPow M γ (n - 1)) ρ (αs n ρ) = dPow M γ n ρ) →
      ∀ x : ℝ, 0 < x →
        twAdmissible M i (Set.Ici 0) N x
            (markovStrategy M (fun _ => i) x M.Q0 (fun n p => p.1 • αs (N - n) p.2)) ∧
          BauerleRiederMDP.RegimeSwitching.eint (M.returnLaw M.Q0 N) (fun r => ((1 / γ * (wealth (fun _ => i) x
              (markovStrategy M (fun _ => i) x M.Q0 (fun n p => p.1 • αs (N - n) p.2)) N r)
                ^ γ : ℝ) : EReal)) =
            twValue M i (Set.Ici 0) (fun x => 1 / γ * x ^ γ) N x) := by sorry

end BauerleRiederMDP.PartialObs
