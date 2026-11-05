-- Prove2me | Theorems.Thm_BauerleRiederMDP_PartialObs_theorem_6_1_1
-- name    : BauerleRiederMDP.PartialObs.theorem_6_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:05:25.8312+00:00
-- url     : https://prove2.me/theorems/4784dbe2-422d-4b87-80aa-0a898e9809e3
-- title:
--   Theorem 6.1.1 — terminal wealth under partial observation: Bellman equation in $(x,\rho)$ (corrected: $D(x)$ independent of $y$; maximizers need closed $D(x)$ or $U^\prime(0+)=\infty$)
-- statement:
--   Consider the terminal wealth problem with partial observation of Section 6.1. A bond has constant interest rate $i\ge0$; $d$ stocks have relative risk $R_{n+1}$ whose law $Q^R(\cdot\mid Y_n)$ depends on a hidden Markov chain $(Y_n)$ on a standard Borel space $E_Y$ with transition $Q^Y$ and prior $Q_0$, as in (6.1), with densities of $Q^R$ and $Q^Y$. The investor has a utility function $U$ (strictly increasing, strictly concave, continuous) on $\operatorname{dom}U=[0,\infty)$ or $(0,\infty)$, observes only the stock prices, and Assumption (FM) holds: no arbitrage for every hidden state, a support of $R(y)$ independent of $y$, and $\sup_y\mathbb E\|R(y)\|<\infty$. Assume moreover that the sets $\{a\mid(1+i)(x+a\cdot R(y))\in\operatorname{dom}U\ \text{a.s.}\}$ do not depend on $y$, so that the admissible investments $D(x)$ are well defined.
--
--   Let $J_n(x,\rho)$ be the value functions of the filtered Markov Decision Model on $E_X\times\mathbb P(E_Y)$, $E_X=\operatorname{dom}U$, let $\Phi$ be the Bayes operator and $\mu_n(\cdot\mid h_n)$ the filter. Then:
--
--   1. For every $n$ and every $\rho\in\mathbb P(E_Y)$ the function $x\mapsto J_n(x,\rho)$ is finite, strictly increasing, strictly concave and continuous on $\operatorname{dom}U$.
--   2. The value functions satisfy the Bellman equation: for $(x,\rho)\in E_X\times\mathbb P(E_Y)$,
--   $$
--   J_0(x,\rho)=U(x),\qquad J_n(x,\rho)=\sup_{a\in D(x)}\int\!\!\int J_{n-1}\big((1+i)(x+a\cdot z),\Phi(\rho,z)\big)\,Q^R(dz\mid y)\,\rho(dy).
--   $$
--   3. For every horizon $N$ and initial wealth $x>0$ the maximal value of the terminal wealth problem
--   $$
--   \mathbb E_x U(X^\varphi_N)\to\max,\qquad \varphi\ \text{an }(\mathcal F^S_n)\text{-adapted portfolio strategy},\ X^\varphi_N\in\operatorname{dom}U\ \text{a.s.}\tag{6.2}
--   $$
--   is $J_N(x,Q_0)$.
--   4. If $\operatorname{dom}U=[0,\infty)$, or $D(x)$ is closed for every $x\in\operatorname{dom}U$, or $U'(0+)=+\infty$ (in the sense that for every $K$ there is $\delta>0$ with $U(t)-U(s)\ge K(t-s)$ whenever $0<s<t<\delta$), then for every $n\ge1$ there exists a maximizer $f^*_n$ of $J_{n-1}$. For every choice of maximizers the portfolio strategy $(f_0,\dots,f_{N-1})$ with $f_n(h_n):=f^*_{N-n}\big(x_n,\mu_n(\cdot\mid h_n)\big)$, $h_n=(x_0,a_0,z_1,x_1,\dots,z_n,x_n)$, is admissible and optimal for (6.2) from every initial wealth $x>0$.
--
--   The theorem reduces the partially observed portfolio problem to a fully observed one whose state is the wealth together with the filter, and shows that the competitors of (6.2), which may use the whole observed history, do no better than this reduced model.
--
--   Differences from the source:
--   - correction: "in view of FM (ii) $D(x)$ does not depend on $y\in E_Y$" → the hypothesis that the sets $\{a\mid(1+i)(x+a\cdot R(y))\in\operatorname{dom}U\ \text{a.s.}\}$ coincide for all $y$; reason: for $\operatorname{dom}U=(0,\infty)$ the constraint is open and (FM)(ii) does not imply it, and then d) fails: with $d=1$, $i=0$, $E_Y=\{1,2\}$, $Q^Y(\cdot\mid y)=\delta_y$, $Q_0=\delta_1$, $U=\sqrt{\cdot}$ on $(0,\infty)$, $Q^R(\cdot\mid1)=\tfrac12\mathrm{Unif}[-\tfrac12,1]+\tfrac12\delta_1$ and $Q^R(\cdot\mid2)=\tfrac12\mathrm{Unif}[-\tfrac12,1]+\tfrac14\delta_1+\tfrac14\delta_{-1/2}$ (same support, no arbitrage, densities with respect to Lebesgue measure plus two atoms), the intersection over $y$ of these sets at $x=1$ is $(-1,2)$, and at $\rho=\delta_1$ the function $a\mapsto\mathbb E\sqrt{1+aR(1)}$ is strictly increasing on $[-1,2]$, so no maximizer of $J_0$ exists; for $\operatorname{dom}U=[0,\infty)$ the hypothesis follows from (FM)(ii)
--   - correction: d) "There exists a maximizer $f^*_n$ of $J_{n-1}$", for every utility function on $\operatorname{dom}U=(0,\infty)$ → existence asserted when $\operatorname{dom}U=[0,\infty)$, or $D(x)$ is closed for all $x\in\operatorname{dom}U$, or $U'(0+)=+\infty$; reason: the printed claim is false: with $|E_Y|=1$, $d=1$, $i=0$, $\mathbb P(R=-\tfrac12)=\tfrac1{10}$, $\mathbb P(R=1)=\tfrac9{10}$ and $U(x)=\log(1+x)$ on $(0,\infty)$, every assumption holds, $D(1)=(-1,2)$, and $a\mapsto\tfrac1{10}\log(2-\tfrac a2)+\tfrac9{10}\log(2+a)$ is strictly increasing on $(-1,2)$ (its derivative at $2$ is $\tfrac{7}{40}>0$ and it is concave), so no maximizer of $J_0$ exists; the book's proof of Theorem 4.1.1 treats the level sets as closed, which fails when $D(x)$ is not closed; parts a), b), c) and optimality of every choice of maximizers are unchanged
--   - reading: a) "strictly increasing, strictly concave and continuous in $x$" → $J_n(\cdot,\rho)$ is finite on $\operatorname{dom}U$, strictly increasing and continuous as an extended-real function, and strictly concave as a real function; reason: strict concavity is a statement about real values; the value functions are real-valued on $E$ (bounded above by the bounding function, below by the all-bond strategy)
--   - reading: d) "There exists a maximizer $f^*_n$ of $J_{n-1}$ and the portfolio strategy … is optimal" → existence of a maximizer for each $n\ge1$, and optimality of the strategy built from every choice of maximizers; reason: as in Theorem 5.3.3 b), from which the book derives d), any sequence of maximizers yields an optimal policy
--   - encoding: $(\mathcal F^S_n)$-adapted strategies and observable histories $h_n$ → measurable functions of the observed returns $(R_1,\dots,R_n)$; reason: $\mathcal F^S_n=\sigma(R_1,\dots,R_n)$ (Doob–Dynkin), and $h_n$ is a function of $x_0$, the strategy and the returns
--   - encoding: $J_n$, the value functions of the filtered model, a supremum over $\Pi_N$ (p.158) → supremum over Markov policies of measurable decision rules on $E$ of the expected utility under the law of the return path of the filtered model; reason: the book notes on p.159 (cf. Theorem 2.2.3) that history-dependent policies of the filtered model give the same value
--   - encoding: expectations and values in $[-\infty,\infty)$ → extended reals with $\int f=\int f^+-\int f^-$; reason: Lean convention; the positive parts are finite here
--   - encoding: Bayes operator undefined where its normalizing constant is $0$ or $\infty$ → defined as $\rho$ there; reason: a null set of $z$ under the predictive law, so no integral changes
--   - encoding: $E_Y$ a Borel subset of a Polish space → $E_Y$ a standard Borel space; reason: the two classes coincide up to isomorphism
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 6.1.1, p.177 (PDF 190); setting §6.1, pp.175–177 (PDF 188–190); utility functions Definition 3.4.1, p.70 (PDF 84)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_FM61
import Definitions.Def_BauerleRiederMDP_PartialObs_IsUtility
import Definitions.Def_BauerleRiederMDP_PartialObs_J
import Definitions.Def_BauerleRiederMDP_PartialObs_twValue
import Definitions.Def_BauerleRiederMDP_PartialObs_IsMaximizer
import Definitions.Def_BauerleRiederMDP_PartialObs_markovStrategy

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Theorem 6.1.1** (terminal wealth problem with partial observation).
Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 6.1.1,
p.177 (PDF 190), with the model of §6.1, pp.175–177 (PDF 188–190):
"For the multiperiod terminal wealth problem with partial observation it holds:
a) The value functions `J_n(x, ρ)` are strictly increasing, strictly concave and continuous in
`x ∈ dom U` for all `ρ ∈ IP(E_Y)`.
b) The value functions can be computed recursively by the Bellman equation, i.e. for
`(x, ρ) ∈ E_X × IP(E_Y)` it holds `J_0(x, ρ) = U(x)`,
`J_n(x, ρ) = sup_{a ∈ D(x)} ∫ ∫ J_{n−1}((1 + i)(x + a · z), Φ(ρ, z)) Q^R(dz|y) ρ(dy)`.
c) The maximal value of problem (6.2) is given by `J_N(x, Q_0)`.
d) There exists a maximizer `f*_n` of `J_{n−1}` and the portfolio strategy `(f_0, …, f_{N−1})` is
optimal for the `N`-stage terminal wealth problem (6.2) where
`f_n(h_n) := f*_{N−n}(x_n, μ_n(·|h_n))`, `h_n = (x_0, a_0, z_1, x_1, … z_n, x_n)`."

Hypotheses: `E_Y` standard Borel; interest rate `i ≥ 0` (§3.1, p.60); `dom U = [0, ∞)` or
`(0, ∞)` and `U` a utility function (Definition 3.4.1); Assumption (FM) of §6.1; and `hD`: the
set `{a | (1 + i)(x + a · R(y)) ∈ dom U a.s.}` does not depend on `y`, which the book asserts on
p.177 ("in view of FM (ii) `D(x)` does not depend on `y ∈ E_Y` and hence `D(x)` is well-defined").

**Formalization Note.**
* `hD` is a correction: for `dom U = [0, ∞)` it follows from (FM)(ii), but for `dom U = (0, ∞)`
  the constraint `x + a · z > 0` is open and two laws with the same support can disagree on it (an
  atom on the boundary of one of them), and then d) fails (see the mission notes).
* The existence of maximizers in d) carries a second correction: it is asserted when
  `dom U = [0, ∞)`, or `D(x)` is closed for all `x ∈ dom U`, or `U'(0+) = +∞` (the last disjunct,
  written with difference quotients, includes `U(0+) = −∞`, so log and negative power utilities).
  Without one of these it is false, even for `|E_Y| = 1`: `d = 1`, `i = 0`,
  `P(R = −1/2) = 1/10`, `P(R = 1) = 9/10`, `U(x) = log(1 + x)` on `(0, ∞)` give `D(1) = (−1, 2)` and
  `a ↦ E U(1 + aR)` strictly increasing there, so the supremum is not attained. (The book's
  proof of Theorem 4.1.1 takes the level sets closed, which fails when `D(x)` is not closed.)
  a), b), c) and the optimality of every choice of maximizers need no such condition.
* a) is stated as: `J_n(·, ρ)` is finite on `dom U`, strictly increasing and continuous as an
  `EReal`-valued function, and strictly concave as a real function.
* c) and d) are stated for initial wealth `x > 0` (p.176). Optimality in d) means the strategy is
  admissible for (6.2) and attains `twValue`; d) is stated for every choice of maximizers. -/
theorem theorem_6_1_1 {EY : Type*} [MeasurableSpace EY] [StandardBorelSpace EY] {d : ℕ}
    (M : Market EY d) (i : ℝ) (hi : 0 ≤ i) (domU : Set ℝ)
    (hdomU : domU = Set.Ici 0 ∨ domU = Set.Ioi 0) (U : ℝ → ℝ) (hU : IsUtility domU U)
    (hFM : FM61 M)
    (hD : ∀ (x : ℝ) (y y' : EY),
      {a : Fin d → ℝ | ∀ᵐ z ∂M.QR y, (1 + i) * (x + a ⬝ᵥ z) ∈ domU} =
        {a : Fin d → ℝ | ∀ᵐ z ∂M.QR y', (1 + i) * (x + a ⬝ᵥ z) ∈ domU}) :
    (∀ (n : ℕ) (ρ : ProbabilityMeasure EY),
      (∀ x ∈ domU, J M i domU U n x ρ ≠ ⊥ ∧ J M i domU U n x ρ ≠ ⊤) ∧
        StrictMonoOn (fun x => J M i domU U n x ρ) domU ∧
        StrictConcaveOn ℝ domU (fun x => (J M i domU U n x ρ).toReal) ∧
        ContinuousOn (fun x => J M i domU U n x ρ) domU) ∧
    (∀ x ∈ domU, ∀ ρ : ProbabilityMeasure EY, J M i domU U 0 x ρ = ((U x : ℝ) : EReal)) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ x ∈ domU, ∀ ρ : ProbabilityMeasure EY,
      J M i domU U n x ρ = ⨆ a ∈ Dset M i domU x, bellmanQ M i (J M i domU U (n - 1)) x ρ a) ∧
    (∀ (N : ℕ) (x : ℝ), 0 < x → twValue M i domU U N x = J M i domU U N x M.Q0) ∧
    ((domU = Set.Ici 0 ∨ (∀ x ∈ domU, IsClosed (Dset M i domU x)) ∨
        ∀ K : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, 0 < s → s < t → t < δ → K * (t - s) ≤ U t - U s) →
      ∀ n : ℕ, 1 ≤ n → ∃ f : ℝ × ProbabilityMeasure EY → Fin d → ℝ,
        IsMaximizer M i domU (J M i domU U (n - 1)) f) ∧
    (∀ (N : ℕ) (fstar : ℕ → ℝ × ProbabilityMeasure EY → Fin d → ℝ),
      (∀ n : ℕ, 1 ≤ n → n ≤ N → IsMaximizer M i domU (J M i domU U (n - 1)) (fstar n)) →
      ∀ x : ℝ, 0 < x →
        twAdmissible M i domU N x
            (markovStrategy M (fun _ => i) x M.Q0 (fun n => fstar (N - n))) ∧
          BauerleRiederMDP.RegimeSwitching.eint (M.returnLaw M.Q0 N) (fun r => ((U (wealth (fun _ => i) x
              (markovStrategy M (fun _ => i) x M.Q0 (fun n => fstar (N - n))) N r) : ℝ) :
                EReal)) = twValue M i domU U N x) := by sorry

end BauerleRiederMDP.PartialObs
