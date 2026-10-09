-- Prove2me | Theorems.Thm_FastCLO_LowerBound_theorem_7
-- name    : FastCLO.LowerBound.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:00.748507+00:00
-- url     : https://prove2.me/theorems/cc2a96e7-4b82-4b29-8d2a-6e912b6bf3a5
-- title:
--   Theorem 7 — any algorithm choosing from a class of Natarajan dimension η has regret ≥ (ρ(Z)/2e⁴)((η−1)/n)^{(1+α)/(2+α)} on some margin-α instance
-- statement:
--   Fix $\alpha \ge 0$, a polytope $\mathcal Z \subseteq \mathbb R^d$ with $\sup_{z\in\mathcal Z}\|z\| \le B$ and extreme points $\mathcal Z^\angle$, and a class $\Pi$ of policies $\mathbb R^p \to \mathcal Z^\angle$ of Natarajan dimension at least $\eta \ge 1$. Let $n \ge 2^{2+\alpha}(\eta - 1)$, and fix any algorithm that maps a sample $\mathcal D$ of size $n$ to a policy $\hat\pi_{\mathcal D} \in \Pi$.
--
--   Then there is a distribution of $(X, Y) \in \mathbb R^p \times \{y : \|y\| \le 1\}$ such that
--   1. some policy in $\Pi$ is optimal: there is $\pi^* \in \Pi$ with $\pi^*(x) \in \arg\min_{z\in\mathcal Z} f^*(x)^\top z$ for every $x$, where $f^*(x) = \mathbb E[Y\mid X=x]$;
--   2. Assumption 2 holds with the given $\alpha$ and $\gamma = B/\rho(\mathcal Z)$, i.e. $\mathbb P_X(0 < \Delta(X) \le \delta) \le (\delta/\rho(\mathcal Z))^\alpha$ for all $\delta > 0$;
--   3. when $\mathcal D$ consists of $n$ i.i.d. draws of $(X, Y)$,
--   $$\mathrm{Regret}(\hat\pi) \;\ge\; \frac{\rho(\mathcal Z)}{2e^4}\Big(\frac{\eta-1}{n}\Big)^{\frac{1+\alpha}{2+\alpha}}.$$
--
--   Together with Theorem 6 of the paper (ERM attains $O\big((\eta\log(|\mathcal Z^\angle|+1)\log(n+1)/n)^{(1+\alpha)/(2+\alpha)}\big)$), this shows that the fast rate in $n$ and $\eta$ under the noise condition cannot be improved, up to logarithmic factors, by any algorithm that only uses well-specification of the policy class.
--
--   **Formalization Note** The paper prints "there exists $\mathbb P$ … such that for any $n \ge 2^{2+\alpha}(\eta-1)$"; the hard distribution of the proof depends on $n$, so the statement is formalized as "for every $n$ and every algorithm there exists a distribution". The hypothesis $\eta \ge 1$ excludes the empty case $\eta = 0$, where $\eta - 1 < 0$; at $\eta = 1$ the bound is $0$. The instance is a pair (law of $X$, Markov kernel of $Y$ given $X$) with $\|Y\| \le 1$; the regret is measured against the optimal value, as in the model file. No measurability is assumed of the algorithm.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Theorem 7, §3.1, p. 9 (proof in A.4.4, pp. 28–30)

import Mathlib
import Definitions.Def_FastCLO_LowerBound_Model
import Definitions.Def_FastCLO_LowerBound_NatShatters
import Definitions.Def_FastCLO_LowerBound_Rho

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.LowerBound

/-- Theorem 7 (Hu, Kallus, Mao, arXiv:2011.03030v3, §3.1, p. 9): fix `α ≥ 0`, a polytope `Z`, a
policy class `Π ⊆ [ℝ^p → Z∠]` of Natarajan dimension at least `η`, and `n ≥ 2^{2+α}(η − 1)`. For
every algorithm mapping data `D` of size `n` to a policy `π̂_D ∈ Π` there is an instance `(X, Y)`
with `‖Y‖ ≤ 1`, an optimal policy `π* ∈ Π`, and the noise condition (7) with the given `α` and
`γ = B/ρ(Z)`, on which `Regret(π̂) ≥ (ρ(Z)/(2e⁴))((η − 1)/n)^{(1+α)/(2+α)}`.

Formalization Note:
* Quantifier order: the page prints "there exists P … such that for any n ≥ …"; the proof's hard
  distribution depends on `n` (through `ζ = ((η−1)/n)^{1/(2+α)}`, p. 28), so the statement is
  `∀ n, ∀ algorithm, ∃ instance`, as proved.
* `1 ≤ η`: with `η = 0` the hypothesis is empty and `η − 1 < 0`; with `η = 1` the bound is `0`.
* `π* ∈ Π` is stated as: some `π ∈ Π` is optimal at every `x`.
* The instance is a pair (law of `X`, conditional law of `Y`), `f*` is the conditional mean, and the
  regret is measured against the optimal value; see `Def_FastCLO_LowerBound_Model`.
* No measurability is required of the algorithm. -/
theorem theorem_7 (α : ℝ) (hα : 0 ≤ α) (p d : ℕ) (P : Polytope d) (Pi : Set (Vec p → Vec d))
    (hPi : ∀ π ∈ Pi, IsPolicy P π) (η : ℕ) (hη : 1 ≤ η) (hsh : NatShatters Pi η)
    (n : ℕ) (hn : (2 : ℝ) ^ (2 + α) * ((η : ℝ) - 1) ≤ n)
    (alg : (Fin n → Vec p × Vec d) → Vec p → Vec d) (halg : ∀ D, alg D ∈ Pi) :
    ∃ I : Instance p d,
      (∃ πs ∈ Pi, ∀ x, πs x ∈ Zstar P I x) ∧
      NoiseCond P I α (P.B / rho P) ∧
      rho P / (2 * Real.exp 4) * (((η : ℝ) - 1) / n) ^ ((1 + α) / (2 + α)) ≤ regret P I n alg := by sorry

end FastCLO.LowerBound
