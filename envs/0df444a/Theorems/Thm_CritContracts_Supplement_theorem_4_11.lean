-- Prove2me | Theorems.Thm_CritContracts_Supplement_theorem_4_11
-- name    : CritContracts.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:00:34.323446+00:00
-- url     : https://prove2.me/theorems/cd594aa5-e34e-4abb-bd58-464d2b9d4d4e
-- title:
--   Theorem 4.11 — $2^{\Omega(m)}$ value or $\mathrm{NE}^\star$ queries are needed for a $64/63$-approximate contract with gross-substitutes rewards and $O(m)$ critical contracts
-- statement:
--   For $m$ large enough, suppose that there is an algorithm with access to an optimal equilibria oracle, such that on every two-agent instance with $m=|T|$ actions, a gross-substitutes reward function, and $O(m)$ critical contracts in $[0,1]^2$, it outputs a $64/63$-approximate contract with probability at least $2/3$. Then on at least one such instance, this algorithm requires $2^{\Omega(m)}$ value or $\mathrm{NE}^\star$ oracle queries.
--
--   Precisely: there are absolute constants $C\in\mathbb N$, $c>0$ and $m_0$ such that for every $m\ge m_0$ and every randomized adaptive algorithm $\mathcal A$ with value queries $f(S)$ and optimal equilibria queries $\mathrm{NE}^\star(\alpha)$, $\alpha\in[0,1]^2$: if on every two-agent instance with $m$ actions, a normalized, monotone, $[0,1]$-valued gross-substitutes reward, nonnegative costs and at most $Cm$ critical contracts in $[0,1]^2$, $\mathcal A$ outputs with probability at least $2/3$ a contract $\alpha\in[0,1]^2$ such that some $S\in\mathrm{NE}(\alpha)$ has
--   $$u_P(\alpha,S)\ \ge\ \tfrac{63}{64}\,\mathrm{OPT},$$
--   then on some such instance some run of $\mathcal A$ asks at least $2^{cm}$ queries.
--
--   So, for gross-substitutes rewards, efficient equilibrium selection and few critical contracts do not suffice: locating the critical contracts is itself hard.
--
--   **Formalization Note** The bound is information-theoretic: the algorithm is unrestricted (no running-time bound, real queries and outputs), it knows the owners and costs, and the $\mathrm{NE}^\star$ oracle returns entire argmax sets.
--
--   Differences from the source:
--
--   - encoding: an algorithm with value and optimal equilibria oracle access → QueryAlg: an arbitrary adaptive randomized strategy over value queries f(S) and NE★(α) queries; queries at vectors outside [0,1]² receive the empty set; reason: the lower bound is information-theoretic (p.26); the paper allows NE★ queries only at contracts
--   - encoding: for m large enough; O(m) critical contracts; 2^{Ω(m)} queries → ∃ C ∈ ℕ, c > 0, m₀ such that for all m ≥ m₀: at most C·m critical contracts, at least 2^{c·m} queries; reason: the meaning of the asymptotic notation with absolute constants
--   - encoding: this algorithm requires 2^{Ω(m)} queries on some instance → some run of the algorithm on some instance of the class asks at least 2^{c·m} queries; reason: negation of a worst-case bound of Q queries on every run, the form used in the proof (p.68)
--   - encoding: a 64/63-approximate contract → a contract α ∈ [0,1]² with some S ∈ NE(α) such that u_P(α, S) ≥ (63/64)·OPT; reason: approximation measured at the principal-optimal equilibrium of the output contract (§2 γ-approximation; the proof requires the output to be the hidden optimal contract)
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Definition 4.10 and Theorem 4.11, p.26 (PDF p.27); proof Appendix F, F.6, p.68 (PDF p.69)

import Mathlib
import Definitions.Def_CritContracts_IsSupermodular
import Definitions.Def_CritContracts_Supplement_IsGrossSubstitutes
import Definitions.Def_CritContracts_Supplement_QueryAlg

set_option autoImplicit false

namespace CritContracts.Supplement

/-- **Theorem 4.11** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial
Contracts*, STOC 2027 submission (manuscript sha256 430be35c…), §4.2, p.26, PDF p.27): for `m` large enough,
suppose that there is an algorithm with access to an optimal equilibria oracle, such that on every two-agent
instance with `m = |T|` actions, a gross-substitutes reward function, and `O(m)` critical contracts in `[0,1]²`, it
outputs a `64/63`-approximate contract with probability at least `2/3`. Then on at least one such instance, this
algorithm requires `2^{Ω(m)}` value or `NE★` oracle queries.

There are absolute constants `C ∈ ℕ`, `c > 0` and `m₀` such that for every `m ≥ m₀` and every randomized adaptive
query algorithm `A` (value queries `f(S)` and optimal equilibria queries `NE★(α)`, `α ∈ [0,1]²`): if on every
two-agent instance with actions `Fin m`, normalized monotone gross-substitutes `[0,1]`-valued reward, nonnegative
costs and at most `C·m` critical contracts in `[0,1]²`, `A` outputs with probability at least `2/3` a contract
`α ∈ [0,1]²` with some `S ∈ NE(α)` such that `u_P(α, S) ≥ (63/64)·OPT`, then on some such instance some run of `A`
asks at least `2^{c·m}` queries.

**Formalization Note** The lower bound is information-theoretic (p.26): `A` is an arbitrary `QueryAlg` (no
running-time restriction; it knows `m`, the owners and the costs, which are identical across the paper's hard
family). `64/63`-approximate refers to the principal-optimal equilibrium at the output contract (the proof requires
the output to be the hidden optimal contract, p.68). `NE★` answers are entire argmax sets, ties included
(Definition 4.10). "At most `C·m` critical contracts" is the `encard` of the set of contracts in `[0,1]²` critical
for some profile. The conclusion asks for one run with many queries, the negation of "at most `Q` queries on every
run" used in the proof (p.68). `OPT` is `CritContracts.Model.OPT`. -/
theorem theorem_4_11 :
    ∃ C : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ A : QueryAlg m,
      (∀ M : Model (Fin 2) (Fin m), IsNormalized M.f → IsMonotone M.f → IsUnitValued M.f →
          IsGrossSubstitutes M.f → (∀ j, 0 ≤ M.c j) → (criticalContracts M).encard ≤ ((C * m : ℕ) : ℕ∞) →
          (2 / 3 : ENNReal) ≤ successProb A M
            (fun α => IsContract α ∧ ∃ S : Finset (Fin m), M.IsNE α S ∧ (63 / 64 : ℝ) * M.OPT ≤ M.principalUtil α S)) →
      ∃ M : Model (Fin 2) (Fin m), IsNormalized M.f ∧ IsMonotone M.f ∧ IsUnitValued M.f ∧
        IsGrossSubstitutes M.f ∧ (∀ j, 0 ≤ M.c j) ∧ (criticalContracts M).encard ≤ ((C * m : ℕ) : ℕ∞) ∧
        ∃ t : ℕ, ∃ r ∈ (queryRun A M t []).support, (2 : ℝ) ^ (c * m) ≤ (r.2 : ℝ) := by sorry

end CritContracts.Supplement
