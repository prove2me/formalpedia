-- Prove2me | Theorems.Thm_AvgPHETH_Supplement_theorem_8_5
-- name    : AvgPHETH.Supplement.theorem_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:04:38.635818+00:00
-- url     : https://prove2.me/theorems/73931f82-491a-4d82-b529-3f668b21dfad
-- title:
--   Theorem 8.5 — with probability one, $\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O$ for the random oracle of §8.1
-- statement:
--   Let $\varepsilon(n)$ be an efficiently computable function with $\varepsilon(n)=o(1)$ and $\varepsilon\ge n^{-o(1)}$, and let $O=A+V$ be the random oracle built from $\varepsilon$ by the staged construction of Section 8.1: in each stage, random restrictions of the construction variables (root bits and selectors of the selector trees), then the assignment of the help oracle $A$ on the queries of that stage, then the completion of the groups that are due, with a diagonalization step on the reserved groups. Then, with probability one,
--
--   $$\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O .$$
--
--   The help oracle $A$ answers a query about an alternating computation only once the answer no longer depends on the undetermined part of $V$; the theorem says that this is enough to solve every distributional problem of the polynomial hierarchy in average polynomial time relative to $O$. Together with Theorem 8.7 it yields the relativization barrier of Theorem 1.5.
--
--   **Formalization Note** The oracle is a function of the construction data (the function $\varepsilon$, a numbering of machines, the enumeration of triples, a selection rule, the reserved lengths) and of independent uniform seeds; the statement is for all admissible data and seeds, and "with probability one" is "for almost every $\omega$".
--
--   Differences from the source:
--   - reading: the oracle $O$ of the construction of §8.1, whose enumeration $(k_s,M_s,m_s)_s$, reserved lengths $n_s$ and lexicographic order are left to be chosen → for every choice: every enumeration of all triples with each appearing infinitely often, every sequence $n_s$ satisfying (a)–(d), every rule selecting one of the disagreeing pairs in step 3(b)iii; reason: the page fixes none of them; the statement is asserted for each admissible choice, which includes the page\'s
--   - reading: "an enumeration of all triples $(k,M,m)$" and codes $\langle M,d\rangle$ of machines → a numbering $i\mapsto M_i$ of oracle machines in which every machine occurs up to its acceptance behaviour (same accepting runs for every oracle, clock and input); $M_s=M_{i_s}$ and $\langle M_i,d\rangle=(1^i,1^d)$; the statement holds for every such numbering; reason: the published machine model has arbitrary alphabet and state types, so its machines form a proper class and have no enumeration; the construction and both proofs use a machine only through its accepting runs
--   - reading: $\varepsilon$ "efficiently computable", $\varepsilon(n)=o(1)$, "$\varepsilon\ge n^{-o(1)}$ without loss of generality" (§8.1, p.38) → $\varepsilon(n)>0$ for all $n$; $\varepsilon(n)\to0$; $g(n)=\max\{16,\lceil\log_2(1/\varepsilon(n))\rceil\}$ computable from $1^n$ in time $n^e+e$; for every $\delta>0$, $\varepsilon(n)\ge n^{-\delta}$ for all large $n$; reason: §8.1 fixes $\varepsilon$ with these properties for the whole section; positivity is presupposed by $\log(1/\varepsilon(n))$; the construction uses $\varepsilon$ only through $g$
--   - encoding: "with probability one" over the random restrictions of the construction → for almost every $\omega$, for any family of independent seeds uniform on $[0,1]$, one per stage, variable and channel, on any probability space; a restriction round is a deterministic function of its seeds and the current assignment (priorities choose the surviving subset, the other seeds the values); reason: conditionally on the earlier rounds this is the $p_j$-random restriction of Definition 4.4, independently for each family, group and stage
--   - encoding: "an appropriate encoding" of $V$-queries, an unspecified encoding of $A$-queries and of the answer $\bot$, and $O=A+V$ → $V_k$-query $(x,y_1,\dots,y_k)$ ↦ binary tuple code of $(1^k,x,y_1,\dots,y_k)$; $A$-query ↦ tuple code $q$ of $(1^i,1^d,u,1^{T^{16}})$, with $0q\in O$ iff $A(q)\ne\bot$ and $1q\in O$ iff $A(q)=1$; $A+V$ is the published join; reason: linear-time decodable encodings with valid $V$-queries of length $O(|x|)$, as the page requires; they change no class
--   - encoding: oracle bits not yet fixed when $f_q$ (step 2(a)) and $O_\alpha$ (step 3(b)) are formed → unassigned $A$-queries are answered $0$, unassigned variables of other groups get the empty string; reason: Proposition 8.3 shows these bits are never read within the clock, so the default changes nothing
--   - encoding: "lexicographically first possible value" / "lexicographically first valid assignment" → every unset variable of the group gets the all-zeros string of its alphabet; reason: the first element of $\{0,1\}^a$ in lexicographic order
--   - encoding: $\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O$ → $\forall d$, DistSubAvgP O d (published); reason: $\mathrm{DistPH}=\bigcup_d\mathrm{Dist}\Sigma_d^p$ (§4.1)
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 8.5, p.44 (PDF 46); oracle construction of §8.1, pp.38–41 (PDF 40–43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData_oracle
import Definitions.Def_AvgPHETH_Supplement_OracleData_Admissible
import Definitions.Def_AvgPHETH_DistSubAvgP

namespace AvgPHETH.Supplement

open AvgPHETH MeasureTheory

/-- **Theorem 8.5** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.44 (PDF 46)): "With probability one, `DistPH^O ⊆ AvgP^O`",
where `O = A + V` is the random oracle of the construction of §8.1 (pp.38–41, PDF 40–43).

**Formalization Note** The oracle is `D.oracle`, a function of the data `D` of the construction and of
the seeds of its restriction rounds; the statement is for all data and seeds satisfying
`OracleData.Admissible` (the function `ε` of Section 8, a numbering of all machines, an enumeration of
all triples, a selection rule, independent uniform seeds, reserved lengths `n_s` with (a)–(d)). "With
probability one" is `∀ᵐ ω ∂μ`. `DistPH^O ⊆ AvgP^O` is `DistΣ_d^{p,O} ⊆ AvgP^O` for every `d` (the
published `AvgPHETH.DistSubAvgP`). -/
theorem theorem_8_5 (D : OracleData) {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (U : ℕ × CVar × ℕ → Ω → ℝ) (hD : D.Admissible μ U) :
    ∀ᵐ ω ∂μ, ∀ d : ℕ, DistSubAvgP (D.oracle (fun i v c => U (i, v, c) ω)) d := by sorry

end AvgPHETH.Supplement
