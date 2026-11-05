-- Prove2me | Theorems.Thm_BauerleRiederMDP_RegimeSwitching_theorem_4_4_1
-- name    : BauerleRiederMDP.RegimeSwitching.theorem_4_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:29:03.164024+00:00
-- url     : https://prove2.me/theorems/8caeece8-2355-47dc-9faa-4354474dc09a
-- title:
--   Theorem 4.4.1 — regime switching: Bellman equation, concave value functions, optimal policy
-- statement:
--   In the consumption-investment problem with regime switching of §4.4, the environment $(Y_n)$ is an observable Markov chain on a finite set $E_Y$ with transition probabilities $p_{jk}$, the relative risk in environment $j$ is $R(j)$ with law $Q_j$ and $R(j)>-1$ a.s., the interest rate is $i\ge0$ and the discount factor $\beta\in(0,1]$. Assumption (FM) holds: for every $j$ there is no arbitrage ($\varphi\cdot R(j)\ge0$ a.s. implies $\varphi\cdot R(j)=0$ a.s.) and $\mathbb E\|R(j)\|<\infty$. $J_n(x,j)$ denotes the maximal expected discounted utility of consumption and terminal wealth over $n$ periods. Let $U_c,U_p$ be utility functions on $[0,\infty)$. Then:
--
--   1. For every $n$ and $j$ the function $x\mapsto J_n(x,j)$ is finite, strictly increasing, strictly concave and continuous on $[0,\infty)$.
--   2. The value functions satisfy the Bellman equation $J_0(x,j)=U_p(x)$ and
--   $$J_{n+1}(x,j)=\sup_{(c,a)\in D(x,j)}\Big\{U_c(c)+\beta\sum_{k\in E_Y}p_{jk}\int J_n\big((1+i)(x-c+a\cdot z),k\big)\,Q_j(dz)\Big\}.$$
--   3. There are decision rules $f_n^*$, $n\ge1$, that are maximizers of $J_{n-1}$ (they attain the supremum defining $J_n$), and for every sequence of such maximizers and every $N$ the policy $(f_N^*,\dots,f_1^*)$, which uses $f_{N-k}^*$ at time $k$, is optimal for the $N$-stage problem.
--
--   The theorem reduces the regime-switching problem to a sequence of one-period problems of the type of Theorem 4.3.1.
--
--   Differences from the source:
--   - encoding: value functions as suprema of 𝔼^π over policies in the Markov Decision Model → valueFunction of a DisturbanceMDM: supremum over admissible measurable Markov policies of the EReal expectation under the Ionescu–Tulcea path measure; reason: the book's definition (pp.16–18); Markov policies suffice by Theorem 2.2.3
--   - encoding: state space [0, ∞), next wealth (1 + i)(x − c + a·z) → state space ℝ≥0 with next wealth Real.toNNReal((1 + i)(x − c + a·z)); reason: for admissible actions the wealth is ≥ 0 a.s., so the truncation changes no law; it keeps T inside the state space for every z
--   - encoding: J_n strictly increasing, strictly concave and continuous in x → J_n(x, j) ≠ ±∞ for x ≥ 0 and x ↦ (J_n(x, j)).toReal is a utility function on Ici 0; reason: J_n is defined in EReal; the book's J_n are real functions, so finiteness is part of its claim
--   - encoding: sup over (a, c) in the Bellman equation → sup over (c, a) ∈ D(x, j); reason: the admissible actions of the model (p.102)
--   - reading: there exist maximizers f*_n of J_{n−1} and (f*_N, …, f*_1) is optimal → maximizers exist, and every sequence of measurable maximizers gives an optimal policy for every N; reason: the book derives c) from Theorem 2.3.8 c), p.23, whose conclusion is that every sequence of maximizers defines an optimal policy; the stronger of the two readings
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.4.1, p.102 (PDF p.116); model p.102 (PDF p.116); proof p.103 (PDF p.117)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_J
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- **Theorem 4.4.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), pp.102–103, PDF pp.116–117). In the consumption-investment problem
with regime switching (§4.4: finite observable environment chain with transition probabilities
`p_{jk}`, relative risk `R(j)` of law `Q_j` in environment `j`, `R(j) > −1` a.s., interest rate
`i ≥ 0`, discount factor `β ∈ (0, 1]`, Assumption (FM): no arbitrage and `𝔼‖R(j)‖ < ∞` for every
`j`) with utility functions `U_c, U_p` on `[0, ∞)`:
a) the value functions `x ↦ J_n(x, j)` are strictly increasing, strictly concave and continuous;
b) they satisfy the Bellman equation `J_0(x, j) = U_p(x)`,
`J_{n+1}(x, j) = sup_{(c,a) ∈ D(x,j)} {U_c(c) + β ∑_k p_{jk} ∫ J_n((1 + i)(x − c + a · z), k) Q_j(dz)}`;
c) there exist maximizers `f*_n` of `J_{n-1}` (`n ≥ 1`), and for every sequence of maximizers
`(f*_N, …, f*_1)` is optimal for the `N`-stage problem.

**Formalization Note.** `J` is defined from the Markov Decision Model `regimeModel` (Markov
policies, path measure, `EReal` values); a) also asserts that `J_n` is finite on `[0, ∞)`, so
that the utility properties are stated for its real value. In b) and c) the integral is `eint`
and the wealth argument is truncated at `0` by `Real.toNNReal` (it is `≥ 0` for `Q_j`-a.e. `z`
when `(c, a) ∈ D(x, j)`). The policy `(f*_N, …, f*_1)` uses `f*_{N-k}` at time `k`. c) is
read as in Theorem 2.3.8 c), p.23, PDF p.38, from which the book derives it: every sequence of measurable
maximizers defines an optimal policy. -/
theorem theorem_4_4_1 {EY : Type*} [Fintype EY] [MeasurableSpace EY] [DiscreteMeasurableSpace EY]
    {d : ℕ} (M : RegimeMarket EY d) (i : ℝ) (hi : 0 ≤ i) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hR : ∀ j, ∀ᵐ z ∂(M.Q j : Measure (Fin d → ℝ)), ∀ k, -1 < z k)
    (hNA : ∀ j, NoArbitrageLaw (M.Q j : Measure (Fin d → ℝ)))
    (hint : ∀ j, Integrable (fun z : Fin d → ℝ => ∑ k, |z k|) (M.Q j : Measure (Fin d → ℝ)))
    (Uc Up : ℝ → ℝ) (hUc : IsUtilityFunction Uc (Set.Ici 0))
    (hUp : IsUtilityFunction Up (Set.Ici 0)) :
    (∀ n j, (∀ x : ℝ≥0, J M i β Uc Up n x j ≠ ⊤ ∧ J M i β Uc Up n x j ≠ ⊥) ∧
      IsUtilityFunction (fun x : ℝ => (J M i β Uc Up n x.toNNReal j).toReal) (Set.Ici 0)) ∧
    (∀ (x : ℝ≥0) j, J M i β Uc Up 0 x j = (Up x : EReal)) ∧
    (∀ n (x : ℝ≥0) j, J M i β Uc Up (n + 1) x j =
      ⨆ ca ∈ (regimeModel M i β Uc).D 0 (x, j), (Uc ca.1 : EReal) +
        (β : EReal) * ∑ k, (M.p j k : EReal) * eint (M.Q j : Measure (Fin d → ℝ)) (fun z =>
          J M i β Uc Up n (Real.toNNReal ((1 + i) * (x - ca.1 + ∑ l, ca.2 l * z l))) k)) ∧
    (∃ fstar : MarkovPolicy (ℝ≥0 × EY) (ℝ × (Fin d → ℝ)),
      (∀ n, 1 ≤ n → ∀ (x : ℝ≥0) j, fstar.f n (x, j) ∈ (regimeModel M i β Uc).D 0 (x, j) ∧
        (Uc (fstar.f n (x, j)).1 : EReal) +
          (β : EReal) * ∑ k, (M.p j k : EReal) * eint (M.Q j : Measure (Fin d → ℝ)) (fun z =>
            J M i β Uc Up (n - 1) (Real.toNNReal ((1 + i) * (x - (fstar.f n (x, j)).1 +
              ∑ l, (fstar.f n (x, j)).2 l * z l))) k) = J M i β Uc Up n x j)) ∧
    ∀ fstar : MarkovPolicy (ℝ≥0 × EY) (ℝ × (Fin d → ℝ)),
      (∀ n, 1 ≤ n → ∀ (x : ℝ≥0) j, fstar.f n (x, j) ∈ (regimeModel M i β Uc).D 0 (x, j) ∧
        (Uc (fstar.f n (x, j)).1 : EReal) +
          (β : EReal) * ∑ k, (M.p j k : EReal) * eint (M.Q j : Measure (Fin d → ℝ)) (fun z =>
            J M i β Uc Up (n - 1) (Real.toNNReal ((1 + i) * (x - (fstar.f n (x, j)).1 +
              ∑ l, (fstar.f n (x, j)).2 l * z l))) k) = J M i β Uc Up n x j) →
      ∀ N, ∃ π : MarkovPolicy (ℝ≥0 × EY) (ℝ × (Fin d → ℝ)),
        (∀ k < N, π.f k = fstar.f (N - k)) ∧ π.IsAdmissible (regimeModel M i β Uc) 0 N ∧
        ∀ (x : ℝ≥0) j,
          policyValue (regimeModel M i β Uc) (fun s => β ^ N * Up s.1) N π 0 (x, j) =
            J M i β Uc Up N x j := by sorry

end BauerleRiederMDP.RegimeSwitching
