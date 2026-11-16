-- Prove2me | Theorems.Thm_FairKMeans_Supplement_theorem_32
-- name    : FairKMeans.Supplement.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:03:36.390202+00:00
-- url     : https://prove2.me/theorems/25e198b8-faba-43cf-b425-6819332121f6
-- title:
--   Theorem 32 — homogeneous cluster constraints: feasibility criterion, $(2\rho+1+\epsilon)$-approximation, and Proposition 29 with $m\to r$ (corrected: $n\to n+k$ in Proposition 29)
-- statement:
--   Consider $k$-means with homogeneous cluster constraints (Definition 30) on weighted points.
--
--   1. An instance has a feasible solution if and only if $\sum_{p\in P}a_j(p)\ge0$ for every $j\in[r]$, and in this case it also has a feasible solution with an integral assignment matrix.
--   2. Let $\rho\ge1$, $\varepsilon\in(0,1]$ and $\eta=\min\{1/10,\varepsilon/(3\rho)\}$. There is a constant $c$, depending only on $\rho$ and $\varepsilon$, such that for every dimension, every instance with a feasible solution, every pair of exact LP oracles and every $\rho$-approximate weighted $k$-means oracle, the weighted Algorithm 1 with the constraints (40) stops by its own test and returns at most $k$ centers $S$ and a feasible fractional assignment $\phi_S$ with
--   $$\mathrm{Cost}(P,S,\phi_S)\le(2\rho+1+\varepsilon)\,\mathrm{OPT}_{\mathrm{frac}}\le(2\rho+1+\varepsilon)\,\mathrm{OPT};$$
--   it calls the $k$-means oracle once, solves at most $\lceil576/\eta^2\rceil+3\le57604(\rho/\varepsilon)^2$ linear programs, and every linear program, the $k$-means input and the number of real-RAM operations outside the oracles are at most $c\,(n+d+r+k+2)^c$.
--   3. Proposition 29 holds with $m$ replaced by $r$: there is an absolute constant $C$ such that, under the hypotheses of 2, the algorithm solves exactly (iterations)$+2$ linear programs, one per recorded size, and every linear program has at most $C(n+k+1)^{\lceil C\rho/\varepsilon\rceil}$ variables and $C(n+r+1)(n+k+1)^{\lceil C\rho/\varepsilon\rceil}$ constraints, the $k$-means input has at most $C(n+1)^{\lceil C\rho/\varepsilon\rceil}$ points, and the number of operations outside the oracles is at most $C(d+1)(n+k+1)^{\lceil C\rho/\varepsilon\rceil}$.
--
--   The class contains fair $k$-means ($r=2m$, Remark 31), $k$-sparse barycenters, and ratio constraints between groups; Corollary 33 combines it with Theorem 7.
--
--   Differences from the source:
--   - generalization: a number r ≥ 1 of constraints (Definition 30) → r : ℕ, r = 0 included; reason: with r = 0 every clause holds verbatim (no constraint); the Lean statement specializes to the source's for r ≥ 1
--   - reading: n weighted points (Definition 30) → weights w(p) > 0; reason: Section 4 (p.18) gives input points weight 1 except in Section 8, and Remark 44 (p.48) extends the analysis to positive weights, the only weighted case the paper proves; positive weights contain the unit-weight case
--   - encoding: a deterministic polynomial-time algorithm with access to a ρ-approximation algorithm → the weighted Algorithm 1 with constraints (40) (alg1H) as a Lean function of two exact LP oracles and a k-means oracle, in the cost model of footnote 1; reason: the proof (p.37) runs Algorithm 1 with 'fair' read as 'feasible'; real-RAM arithmetic counted, LP and k-means time separate, as in the published Theorem 3
--   - reading: a … algorithm computes → this algorithm, for every exact LP oracle pair and every ρ-approximate k-means oracle; reason: the paper's witness; stronger than an existential
--   - reading: O((ρ/ϵ)²) linear programs; polynomial time → ⌈576/η²⌉ + 3 ≤ 57604(ρ/ϵ)² LPs; ∃ c depending only on (ρ, ϵ) with every LP, the k-means input and the operation count ≤ c·(n+d+r+k+2)^c; reason: the reading of the published Theorem 3 with m replaced by r
--   - reading: Proposition 29 holds with m replaced by r → the published reading of Proposition 29 (FairKMeans.proposition_29: its head and part 2) for the weighted constrained algorithm, with the constraint count C(n+r+1)(n+k+1)^⌈Cρ/ϵ⌉; reason: the formalized algorithm uses the candidate sets of Lemma 15 part 2 in every dimension, which Proposition 29 part 2 bounds; part 1 bounds a different instantiation (the fixed-dimension sets of [Mat00], cited and not constructed), so it does not apply to this algorithm
--   - correction: Proposition 29 part 2: LPs with n^{O(ρ/ϵ)} variables and (n+m)n^{O(ρ/ϵ)} constraints, time d n^{O(ρ/ϵ)} → (n+k+1) in place of n in the LP and time bounds, (n+1) for the k-means input (with m → r); reason: inherited from the published proposition_29: the final LP has n·|S_π| variables and the oracle may return k centers; counterexample n = d = r = 1, a ≡ 1, k → ∞; the proof's 'k ≤ n' (p.36) is never assumed
--   - encoding: the instance has a feasible solution; the LPs are solved exactly → hypotheses HasFeasibleSolution, IsHLPOracle, IsHLP29Oracle in clauses 2 and 3; reason: the setting of the theorem; they keep every assignment of the loop nonnegative, so the k-means oracle receives nonnegative weights
--   - encoding: center sets S ⊂ ℝ^d → indexed families (duplicates allowed); WCS_δ by Lemma 15 part 2 in every dimension; reason: merging duplicate centers keeps (40) and the cost; p.20: part 2 alone suffices for polynomial time
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Theorem 32, p.37 (PDF p.39); proof pp.37–38 (PDF pp.39–40); Proposition 29, p.35 (PDF p.37); Remark 44, p.48 (PDF p.50)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1
import Definitions.Def_FairKMeans_Supplement_Constrained
import Definitions.Def_FairKMeans_Supplement_ConstrainedLP
import Definitions.Def_FairKMeans_Supplement_ConstrainedAlgorithm

namespace FairKMeans.Supplement

open FairKMeans

/-- **Theorem 32 (Homogeneous cluster constraints)**, p.37 (PDF 39); proof pp.37–38
(PDF 39–40). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…).

1. An instance of Definition 30 (weighted points) has a feasible solution if and only if
   `∑_p a_j(p) ≥ 0` for every `j ∈ [r]`, and in this case it also has a feasible solution with an
   integral assignment matrix.
2. Let `ρ ≥ 1`, `ε ∈ (0, 1]` and `η = min{1/10, ε/(3ρ)}`. There is `c` (depending only on `ρ`
   and `ε`) such that for every dimension, every instance with a feasible solution, every exact
   feasible-assignment-LP oracle, every exact LP (29) oracle and every ρ-approximate weighted
   k-means oracle, the weighted Algorithm 1 with constraints (40) stops by its own test, returns
   at most `k` centers `S` and a feasible fractional assignment `φ_S` with
   `Cost(P, S, φ_S) ≤ (2ρ+1+ε) OPT_frac ≤ (2ρ+1+ε) OPT`, calls the k-means oracle once, solves
   at most `⌈576/η²⌉ + 3 ≤ 57604 (ρ/ε)²` linear programs, and every LP, the k-means input and
   the operation count are at most `c (n+d+r+k+2)^c`.
3. Proposition 29 (head and part 2, in the published corrected reading `n → n + k`) holds with
   `m` replaced by `r`.

**Formalization Note.** Clause 3 is the published reading of Proposition 29
(`FairKMeans.proposition_29`) transferred to the weighted constrained algorithm, with the
constraint count `C (n+r+1)(n+k+1)^{⌈Cρ/ε⌉}`; part 1 of Proposition 29 (fixed dimension, via
the cited candidate sets of [Mat00]) is not part of that reading. -/
theorem theorem_32 :
    (∀ (d n r : ℕ) (I : HInstance d n r),
      (HasFeasibleSolution I ↔ ∀ j : Fin r, 0 ≤ ∑ p, I.a j p) ∧
      (HasFeasibleSolution I → ∃ s ≤ I.k, ∃ (S : Fin s → E d) (φ : Fin n → Fin s → ℝ),
        IsAssignment φ ∧ IsIntegral φ ∧ IsFeasible I φ)) ∧
    (∀ (ρ ε : ℝ), 1 ≤ ρ → ε ∈ Set.Ioc (0 : ℝ) 1 →
      ∃ c : ℕ, ∀ (d n r : ℕ) (I : HInstance d n r), HasFeasibleSolution I →
        ∀ (hLP : FairLPOracle d n) (lp29 : LP29Oracle d n) (KM : KMOracle d),
        IsHLPOracle I hLP → IsHLP29Oracle I lp29 → IsRhoApprox ρ I.k KM →
        (alg1H ρ ε I hLP lp29 KM).stopped ∧
        (alg1H ρ ε I hLP lp29 KM).s ≤ I.k ∧
        IsAssignment (alg1H ρ ε I hLP lp29 KM).assign ∧
        IsFeasible I (alg1H ρ ε I hLP lp29 KM).assign ∧
        hcost I (alg1H ρ ε I hLP lp29 KM).centers (alg1H ρ ε I hLP lp29 KM).assign ≤
          (2 * ρ + 1 + ε) * hOPTfrac I ∧
        (2 * ρ + 1 + ε) * hOPTfrac I ≤ (2 * ρ + 1 + ε) * hOPT I ∧
        (alg1H ρ ε I hLP lp29 KM).kmCalls = 1 ∧
        (alg1H ρ ε I hLP lp29 KM).lpCalls ≤ ⌈576 / eta ρ ε ^ 2⌉₊ + 3 ∧
        ((alg1H ρ ε I hLP lp29 KM).lpCalls : ℝ) ≤ 57604 * (ρ / ε) ^ 2 ∧
        (∀ L ∈ (alg1H ρ ε I hLP lp29 KM).lpSizes,
          L.1 + L.2 ≤ c * (n + d + r + I.k + 2) ^ c) ∧
        (alg1H ρ ε I hLP lp29 KM).kmInputSize ≤ c * (n + d + r + I.k + 2) ^ c ∧
        (alg1H ρ ε I hLP lp29 KM).arithOps ≤ c * (n + d + r + I.k + 2) ^ c) ∧
    (∃ C : ℕ, ∀ (ρ ε : ℝ), 1 ≤ ρ → ε ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (d n r : ℕ) (I : HInstance d n r), HasFeasibleSolution I →
        ∀ (hLP : FairLPOracle d n) (lp29 : LP29Oracle d n) (KM : KMOracle d),
        IsHLPOracle I hLP → IsHLP29Oracle I lp29 → IsRhoApprox ρ I.k KM →
        (alg1H ρ ε I hLP lp29 KM).kmCalls = 1 ∧
        (alg1H ρ ε I hLP lp29 KM).lpCalls = (alg1H ρ ε I hLP lp29 KM).iterations + 2 ∧
        (alg1H ρ ε I hLP lp29 KM).lpSizes.length = (alg1H ρ ε I hLP lp29 KM).lpCalls ∧
        (alg1H ρ ε I hLP lp29 KM).lpCalls ≤ ⌈576 / eta ρ ε ^ 2⌉₊ + 3 ∧
        ((alg1H ρ ε I hLP lp29 KM).lpCalls : ℝ) ≤ 57604 * (ρ / ε) ^ 2 ∧
        (∀ L ∈ (alg1H ρ ε I hLP lp29 KM).lpSizes,
          L.1 ≤ C * (n + I.k + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊ ∧
          L.2 ≤ C * (n + r + 1) * (n + I.k + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊) ∧
        (alg1H ρ ε I hLP lp29 KM).kmInputSize ≤ C * (n + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊ ∧
        (alg1H ρ ε I hLP lp29 KM).arithOps ≤
          C * (d + 1) * (n + I.k + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊) := by sorry

end FairKMeans.Supplement
