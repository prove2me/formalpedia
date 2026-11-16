-- Prove2me | Theorems.Thm_AcceptSubcube_Supplement_theorem_4_11
-- name    : AcceptSubcube.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:52:22.702798+00:00
-- url     : https://prove2.me/theorems/cc474825-28c0-42ba-9967-1dba7576ab1d
-- title:
--   Theorem 4.11 — order-three LP barrier: integrality gaps $\Omega(\log q)$ and $\Omega(\log N)$
-- statement:
--   1. There are $c>0$ and $q_0$ such that for every $q\ge q_0$ there are a weighted binary CNF formula $\Phi$ on the variables $x_0,\dots,x_{q-1}$ (each clause has two literals on distinct variables and a nonnegative rational weight) and rational local laws on every set of at most three of the $q$ variables, normalized, consistent and nonnegative, with every literal marginal $\Pr[x_i=1]=1/2$, such that the fractional value $V=\sum_C w_C\Pr[C\text{ violated}]$ is positive and every assignment $x$ satisfies
--   $$C_\Phi(x)\ge c\,\log q\cdot V .$$
--   2. For every $K\ge0$ there are $c_K>0$ and $N_0$ such that for every $N\ge N_0$ there are a complete Min-3-SAT instance $\mathcal I$ on $N$ variables, a center $\tau$ and a radius $1\le r\le N$ with $\mathrm{OPT}(\mathcal I)\ge1$ and
--   $$\mathrm{OPT}(\mathcal I)\ge c_K\,\log N\cdot\big(L^*_{\tau,r}+Kr^3\big),$$
--   where $L^*_{\tau,r}$ is the budgeted Hamming-ball LP value of §4.3 (without the semidefinite constraint).
--
--   This shows that, without the semidefinite constraint, the charging interface of the cubic repair cannot be rounded within a constant factor of the linear relaxation, even on complete instances; it excludes guarantees $C(\hat x)\le A\,L^*_{\tau,r}+Kr^3$ with universal constants.
--
--   **Formalization Note** Local laws are given by rational moments (the published moment parametrization), with nonnegative local probabilities on every set of at most three of the $q$ variables. $\mathrm{OPT}(\mathcal I)$ is the global optimum. Natural logarithms.
--
--   Differences from the source:
--   - reading: Ω(log q); Ω(log N) → a constant c > 0 (c_K > 0, which may depend on K) and a threshold beyond which every q (resp. every N) has such an instance; reason: the stronger of the two readings ('for all large' rather than 'for infinitely many'); the proof's construction reaches every large N by choosing T₀ = (N − q)/4 ≥ q⁴ with q ≡ N mod 4, since Lemma 4.15 and (21) hold for every T₀ ≥ q⁴
--   - reading: weighted binary CNF formulas on q variables → clauses of exactly two literals on distinct variables among x₀,…,x_{q−1}, with nonnegative rational weights; reason: the stronger reading of 'binary'; Proposition 4.14's formula has this form
--   - encoding: rational, consistent order-three local laws → a rational moment list whose local probabilities are nonnegative on every set of at most three of the q variables; reason: the moment parametrization makes normalization and consistency identities (Proof of Lemma 4.7, p.20)
--   - encoding: the integral optimum exceeds the fractional value by a factor Ω(log q) → V > 0 and C_Φ(x) ≥ c log q · V for every x; reason: the paper's fractional value V = m/(2R) is positive; positivity excludes degenerate witnesses such as the empty formula
--   - encoding: OPT(I)/(L*_{τ,r} + Kr³) = Ω(log N) → OPT(I) ≥ 1 and OPT(I) ≥ c_K log N (L*_{τ,r} + Kr³); reason: the ratio written without division: for K > 0 the denominator is positive (r ≥ 1); for K = 0 a zero LP value with OPT ≥ 1 is an infinite ratio, which the source's claim includes; OPT ≥ 1 excludes satisfiable instances, where both sides could vanish (the paper's instances have OPT ≥ T₀m/32 − 2q³ ≥ 1)
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 4.11, p.23 (proof: Lemmas 4.12–4.15, Proposition 4.14, (21), pp.24–25)

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_RelaxFeasible
import Definitions.Def_AcceptSubcube_WCNF
import Definitions.Def_AcceptSubcube_Supplement_CompleteSigned
import Definitions.Def_AcceptSubcube_Supplement_Lstar

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **Theorem 4.11 (Order-three LP barrier).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 4.11, p.23: "There are weighted binary
CNF formulas on q variables with rational, consistent order-three local laws, all literal marginals
equal to 1/2, whose integral optimum exceeds the fractional value by a factor Ω(log q). For every
fixed K ≥ 0 there are complete Min-3-SAT instances on N variables with centers τ and radii r such
that the budgeted Hamming-ball LP value L*_{τ,r} of Section 4.3 satisfies
OPT(I)/(L*_{τ,r} + Kr^3) = Ω(log N)."

1. There are `c > 0` and `q₀` such that for every `q ≥ q₀` there are a weighted CNF `Φ` on the
   variables `0, …, q−1`, every clause of two literals on distinct variables with a nonnegative
   rational weight, and rational moments `L` whose local laws on every set of at most three of the
   `q` variables are nonnegative (normalized and consistent by construction), with every literal
   marginal `P[x_i = 1] = 1/2`, fractional value `V = fracCost L Φ > 0`, and
   `C_Φ(x) ≥ c · log q · V` for every assignment `x`.
2. For every `K ≥ 0` there are `c_K > 0` and `N₀` such that for every `N ≥ N₀` there are a complete
   Min-3-SAT instance `I` on `N` variables, a center `τ` and a radius `1 ≤ r ≤ N` with
   `OPT(I) ≥ 1` and `OPT(I) ≥ c_K · log N · (L*_{τ,r} + K r³)`.

**Formalization Note.** `Ω(log q)` and `Ω(log N)` are read as a positive constant and a threshold
beyond which every `q` (resp. `N`) has such an instance (the stronger reading; `c_K` may depend on
`K`). In part 1 the fractional value is positive, as the paper's `V = m/(2R)`, which excludes the
empty formula. In part 2 the ratio `OPT/(L* + Kr³)` is stated as `OPT ≥ c_K log N (L* + Kr³)` with
`OPT ≥ 1`: for `K > 0` the denominator is positive (`r ≥ 1`), and for `K = 0` a zero LP value with
`OPT ≥ 1` is an infinite gap; `OPT ≥ 1` excludes the satisfiable instances, for which both sides
can vanish. Local laws are the published moment parametrization
(`LocalNonneg 3 q`, `lit1`, `fracCost`); `L*_{τ,r}` is `Lstar 3` (no semidefinite constraint).
`OPT(I)` is the global optimum. Natural logarithms. -/
theorem theorem_4_11 :
    (∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∃ (Φ : WCNF) (L : List (List ℕ × ℚ)),
        (∀ cl ∈ Φ, ∃ a b : ℕ × Bool, cl.2 = [a, b] ∧ a.1 ≠ b.1) ∧
        OnVars Φ (Finset.range q) ∧ NonnegWeights Φ ∧
        LocalNonneg 3 q L ∧ (∀ i < q, lit1 L i true = 1 / 2) ∧
        0 < fracCost L Φ ∧
        ∀ x : ℕ → Bool,
          c * Real.log (q : ℝ) * ((fracCost L Φ : ℚ) : ℝ) ≤ ((cnfCost Φ x : ℚ) : ℝ)) ∧
    (∀ K : ℝ, 0 ≤ K → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ (I : GInst) (τ : Fin I.n → Bool) (r : ℕ),
        I.n = N ∧ CompleteSigned (thr 1) 3 I ∧ 1 ≤ r ∧ r ≤ N ∧
        1 ≤ OPT I ∧
        c * Real.log (N : ℝ) * (Lstar 3 I τ r + K * (r : ℝ) ^ 3) ≤ (OPT I : ℝ)) := by sorry

end AcceptSubcube.Supplement
