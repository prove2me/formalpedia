-- Prove2me | Theorems.Thm_AvgPHETH_Supplement_theorem_8_7
-- name    : AvgPHETH.Supplement.theorem_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:06:40.543671+00:00
-- url     : https://prove2.me/theorems/8d1fe4e4-613a-41cf-b0bf-1c141d5c227a
-- title:
--   Theorem 8.7 — with probability one, $L_k^O\notin\Sigma_k\mathrm{TIME}^O[2^{o(a_k(n))}]$ for every $k\ge1$
-- statement:
--   Let $\varepsilon(n)$ be an efficiently computable function with $\varepsilon(n)=o(1)$ and $\varepsilon\ge n^{-o(1)}$, let $O=A+V$ be the random oracle built from $\varepsilon$ by the staged construction of Section 8.1, and let $L_k^O$ be the language of the inputs $x$ of active length with $\forall y_1\in Y_1(|x|)\,\exists y_2\in Y_2(|x|)\cdots Q_ky_k\in Y_k(|x|):V_k(x,y_1,\dots,y_k)=1$. Then, with probability one, simultaneously for every $k\ge1$,
--
--   $$L_k^O\notin\Sigma_k\mathrm{TIME}^O\big[2^{o(a_k(n))}\big],\qquad a_k(n)=\Big\lfloor\frac n{(g(n)\log n)^k}\Big\rfloor .$$
--
--   Consequently,
--
--   $$\Pi_k^{p,O}\not\subseteq\Sigma_k\mathrm{TIME}^O\Big[2^{\varepsilon(n)\,n/\log^kn}\Big].$$
--
--   So relative to $O$ a $\Pi_k$ language needs $\Sigma_k$ time almost $2^{n/\log^kn}$, which shows that the simulations of Theorem 1.2 cannot be improved by relativizing techniques.
--
--   **Formalization Note** The oracle is a function of the construction data and of independent uniform seeds; the statement is for all admissible data and seeds. Both conclusions, for all $k\ge1$ at once, hold for almost every $\omega$.
--
--   Differences from the source:
--   - reading: the oracle $O$ of the construction of §8.1, whose enumeration $(k_s,M_s,m_s)_s$, reserved lengths $n_s$ and lexicographic order are left to be chosen → for every choice: every enumeration of all triples with each appearing infinitely often, every sequence $n_s$ satisfying (a)–(d), every rule selecting one of the disagreeing pairs in step 3(b)iii; reason: the page fixes none of them; the statement is asserted for each admissible choice, which includes the page\'s
--   - reading: "an enumeration of all triples $(k,M,m)$" and codes $\langle M,d\rangle$ of machines → a numbering $i\mapsto M_i$ of oracle machines in which every machine occurs up to its acceptance behaviour (same accepting runs for every oracle, clock and input); $M_s=M_{i_s}$ and $\langle M_i,d\rangle=(1^i,1^d)$; the statement holds for every such numbering; reason: the published machine model has arbitrary alphabet and state types, so its machines form a proper class and have no enumeration; the construction and both proofs use a machine only through its accepting runs
--   - reading: $\varepsilon$ "efficiently computable", $\varepsilon(n)=o(1)$, "$\varepsilon\ge n^{-o(1)}$ without loss of generality" (§8.1, p.38) → $\varepsilon(n)>0$ for all $n$; $\varepsilon(n)\to0$; $g(n)=\max\{16,\lceil\log_2(1/\varepsilon(n))\rceil\}$ computable from $1^n$ in time $n^e+e$; for every $\delta>0$, $\varepsilon(n)\ge n^{-\delta}$ for all large $n$; reason: §8.1 fixes $\varepsilon$ with these properties for the whole section; positivity is presupposed by $\log(1/\varepsilon(n))$; the construction uses $\varepsilon$ only through $g$
--   - encoding: "with probability one" over the random restrictions of the construction → for almost every $\omega$, for any family of independent seeds uniform on $[0,1]$, one per stage, variable and channel, on any probability space; a restriction round is a deterministic function of its seeds and the current assignment (priorities choose the surviving subset, the other seeds the values); reason: conditionally on the earlier rounds this is the $p_j$-random restriction of Definition 4.4, independently for each family, group and stage
--   - encoding: "an appropriate encoding" of $V$-queries, an unspecified encoding of $A$-queries and of the answer $\bot$, and $O=A+V$ → $V_k$-query $(x,y_1,\dots,y_k)$ ↦ binary tuple code of $(1^k,x,y_1,\dots,y_k)$; $A$-query ↦ tuple code $q$ of $(1^i,1^d,u,1^{T^{16}})$, with $0q\in O$ iff $A(q)\ne\bot$ and $1q\in O$ iff $A(q)=1$; $A+V$ is the published join; reason: linear-time decodable encodings with valid $V$-queries of length $O(|x|)$, as the page requires; they change no class
--   - encoding: oracle bits not yet fixed when $f_q$ (step 2(a)) and $O_\alpha$ (step 3(b)) are formed → unassigned $A$-queries are answered $0$, unassigned variables of other groups get the empty string; reason: Proposition 8.3 shows these bits are never read within the clock, so the default changes nothing
--   - encoding: "lexicographically first possible value" / "lexicographically first valid assignment" → every unset variable of the group gets the all-zeros string of its alphabet; reason: the first element of $\{0,1\}^a$ in lexicographic order
--   - encoding: $L_k^O\notin\Sigma_k\mathrm{TIME}^O[2^{o(a_k(n))}]$ → for every $f:\mathbb N\to\mathbb R$ with $f=o(a_k)$ as $n\to\infty$, $L_k^O\notin\Sigma_k\mathrm{TIME}^O[2^{f(n)}]$; $a_k(n)=\lfloor n/R(n)^k\rfloor$ for every $n$; reason: the meaning of $2^{o(\cdot)}$ in a class bound; only large $n$ matter
--   - reading: $\Sigma_k\mathrm{TIME}^O[t]$ for bounds $t$ that need not be time-constructible → SigmaKTime: $L(x)=\Phi^O_{T,W}(x)$ for all $T,W\ge\lceil c\,t(|x|)\rceil+c$, for some $c\ge1$ and machine $M$; reason: the characterisation of Definition 4.3 (p.15), which is how the proof on p.47 uses the class ("running time and witness length are each at most $T(n)$"); it contains the page\'s class for time-constructible $t$, so the non-membership is at least as strong
--   - encoding: $V_k(x,y_1,\dots,y_k)=1$ in the definition of $L_k^O$; $\Pi_k^{p,O}$; $\log n$ → the induced leaf value $T^k_x(y_1,\dots,y_k)$ of the final assignment; PiPO (complements of the published SigmaPO); $\log_2 n$, with the bound $2^0$ at $n\le1$; reason: $V_k$ outputs exactly this value; two input lengths, absorbed by the threshold of SigmaKTime
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 8.7, p.47 (PDF 49); oracle construction of §8.1, pp.38–41 (PDF 40–43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData_oracle
import Definitions.Def_AvgPHETH_Supplement_OracleData_Admissible
import Definitions.Def_AvgPHETH_Supplement_Lk
import Definitions.Def_AvgPHETH_Supplement_PiPO
import Definitions.Def_AvgPHETH_Supplement_SigmaKTime

namespace AvgPHETH.Supplement

open AvgPHETH MeasureTheory Filter Asymptotics

/-- **Theorem 8.7** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.47 (PDF 49)): "With probability one, simultaneously for
every `k ≥ 1`, `L_k^O ∉ Σ_kTIME^O[2^{o(a_k(n))}]`. Consequently,
`Π_k^{p,O} ⊄ Σ_kTIME^O[2^{ε(n)n/log^k n}]`", where `O = A + V` is the random oracle of the construction
of §8.1 (pp.38–41, PDF 40–43).

**Formalization Note** The oracle is `D.oracle` and `L_k^O` is `Lk` at the final assignment, for all
data and seeds satisfying `OracleData.Admissible`. "With probability one" is `∀ᵐ ω ∂μ`, and both
conclusions, for every `k ≥ 1`, are inside it. `L ∉ Σ_kTIME^O[2^{o(a_k(n))}]` is: `L ∉ Σ_kTIME^O[2^{f(n)}]`
for every `f : ℕ → ℝ` with `f = o(a_k)` as `n → ∞`. `log` is `log₂`; `Σ_kTIME^O[·]` is `SigmaKTime`,
whose threshold `⌈c·t⌉₊ + c` absorbs the lengths `n ≤ 1`, where `log₂ n = 0`. -/
theorem theorem_8_7 (D : OracleData) {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (U : ℕ × CVar × ℕ → Ω → ℝ) (hD : D.Admissible μ U) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, 1 ≤ k →
      (∀ f : ℕ → ℝ, f =o[atTop] (fun n => (aPar D.eps k n : ℝ)) →
        Lk D.eps (D.finalAsg (fun i v c => U (i, v, c) ω)) k ∉
          SigmaKTime (D.oracle (fun i v c => U (i, v, c) ω)) k (fun n => (2 : ℝ) ^ f n)) ∧
      ∃ L ∈ PiPO (D.oracle (fun i v c => U (i, v, c) ω)) k,
        L ∉ SigmaKTime (D.oracle (fun i v c => U (i, v, c) ω)) k
          (fun n => (2 : ℝ) ^ (D.eps n * ((n : ℝ) / Real.logb 2 n ^ k))) := by sorry

end AvgPHETH.Supplement
