-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_theorem_1_1
-- name    : ChengCapClustering.Soft.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:25.121461+00:00
-- url     : https://prove2.me/theorems/b81e40c2-744d-4fab-b713-6d6e3afe1b49
-- title:
--   Theorem 1.1 — uniform soft capacities: $k+\lfloor\varepsilon k\rfloor$ centers, ratio $\beta-(\beta-1)\varepsilon+\delta$ in polynomial time; $\beta=3^z$ (metric), $\beta=\beta^*_z$ ($\mathbb R^d$)
-- statement:
--   For every fixed $\varepsilon\in(0,1]$, there is an algorithm for uniform soft capacities in low dimension with ratio $3-2\varepsilon$ for $k$-median and $9-8\varepsilon$ for $k$-means, or $5-4\varepsilon$ in $\mathbb R^d$. More generally, for every fixed $z\ge1$, the ratio is $\beta-(\beta-1)\varepsilon$, where $\beta=3^z$ in general and $\beta=\beta^*_z$ in $\mathbb R^d$.
--
--   Here (§1.1, §2): an algorithm with ratio $\alpha$ opens at most $K=k+\lfloor\varepsilon k\rfloor$ centers, respects the uniform capacity $U$ exactly, and returns a soft solution of cost at most $\alpha\cdot\mathrm{OPT}$, where $\mathrm{OPT}$ is the optimal cost with at most $k$ centers; all ratios hold up to an arbitrarily small additive $\delta>0$; the algorithms are deterministic and run in polynomial time, counting arithmetic operations and evaluations of $\mathrm{dist}(x,y)^z$ as single steps. "Low dimension" means that the clients $P$ or the finite location set $F$ has doubling dimension at most a fixed $D$; in $\mathbb R^d$ the centers may be anywhere ($F=\mathbb R^d$), the clients have doubling dimension at most $D$, and the output centers are distinct when $\mathrm{OPT}>0$. Standing assumptions: $0<k<n$ and $n\le kU$.
--
--   Formally: (1) for all $D,z,\varepsilon,\delta$ with $z\ge1$, $\varepsilon\in(0,1]$, $\delta>0$ there are a program and a constant $C$ such that on every metric instance (clients $p$, injective nonempty location list $f$, $P$ or $F$ of doubling dimension at most $D$) the program halts within $C(n+m+2)^C(2+\log_2\Delta)^C$ steps with a soft solution of at most $K$ centers in $F$ and cost $\le(3^z-(3^z-1)\varepsilon+\delta)\,\mathrm{OPT}$; (2) likewise in $\mathbb R^d$ within $C(d+1)(n+2)^C(2+\log_2\Delta(P))^C$ steps, with cost $\le(\beta^*_z-(\beta^*_z-1)\varepsilon+\delta)\,\mathrm{OPT}$ and pairwise distinct centers when $\mathrm{OPT}>0$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: "All our ratios hold up to an additive δ > 0 that can be fixed arbitrarily small; we omit δ" → for every δ > 0 a program (depending on δ) with cost ≤ (β − (β−1)ε + δ)·OPT; reason: §1.1, printed p. 2
--   - reading: polynomial time ("(n + |F|)^φ (log Δ)^{O(1)}", degree φ depending only on D, z, ε, δ) → at most C (n+m+2)^C (2 + log₂ Δ)^C steps, Δ the aspect ratio of the listed points of P ∪ F, C depending only on D, z, ε, δ; reason: running-time paragraph of §1.1, printed p. 3
--   - reading: in ℝ^d: degree independent of d, d entering only through coordinate arithmetic; Δ of P ∪ F → at most C (d+1) (n+2)^C (2 + log₂ Δ(P))^C steps, Δ(P) the aspect ratio of the clients; reason: §1.1 and §5.3.3 (printed pp. 3, 31); Δ(P ∪ F) is undefined for F = ℝ^d, so the aspect ratio of the input clients is used
--   - reading: low dimension: P or F has doubling dimension at most a fixed D → IsDoublingWith (range p) D ∨ IsDoublingWith (range f) D (published definition, floor D ≥ 1); the program is not told which side; reason: one algorithm per fixed D; a set of doubling dimension below 1 satisfies the bound 1
--   - reading: ratios 3 − 2ε (k-median), 9 − 8ε (k-means), 5 − 4ε (ℝ^d) → the general ratios β − (β−1)ε + δ with β = 3^z and β = β*_z; reason: the named ratios are the instances z = 1, 2, with β*_1 = 3 and β*_2 = 5 (Proposition 5.4(b))
--   - encoding: OPT, the minimum cost with at most k centers → opt: infimum in ℝ≥0∞ over soft solutions with ≤ k centers; costs compared through ENNReal.ofReal; reason: under n ≤ kU and F ≠ ∅ the infimum is finite and equals the minimum
--   - encoding: an instance (metric space, finite F, multiset P; or P ⊂ ℝ^d, F = ℝ^d) → integer input [n, m, k, U] (resp. [n, d, k, U]); real input [z, ε, δ] followed by the distance matrix of P ∪ F, clients first (resp. the client coordinates); output: center count, center locations (indices into f, resp. coordinates) and the assignment; reason: the input conventions of Appendix C (distance matrix / coordinates); parameters are data because program literals are rational
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Theorem 1.1, printed p. 2 / PDF p. 4 (with §1.1 printed pp. 2–3 and §2 printed pp. 4–5)

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Certificate

open MinSumDimRed.Doubling

universe u

namespace ChengCapClustering.Soft

/-- Theorem 1.1 (Uniform soft capacities), printed p. 2 / PDF p. 4. First conjunct: metric
instances with a finite location set `F` and `P` or `F` of doubling dimension at most `D`, ratio
`3^z − (3^z − 1)ε + δ`. Second conjunct: clients in `ℝ^d` of doubling dimension at most `D`, centers
anywhere in `ℝ^d`, ratio `β*_z − (β*_z − 1)ε + δ`, distinct output centers when `OPT > 0`. In both,
one deterministic program for each fixed `D, z, ε, δ` opens at most `K = k + ⌊εk⌋` centers, respects
the uniform capacity `U` exactly, and runs in polynomially many steps of the arithmetic machine. -/
theorem theorem_1_1 :
    (∀ D z ε δ : ℝ, 1 ≤ z → 0 < ε → ε ≤ 1 → 0 < δ →
      ∃ prog : Program, Admissible prog ∧ ∃ C : ℕ,
        ∀ (V : Type u) [MetricSpace V] (n m k U : ℕ) (p : Fin n → V) (f : Fin m → V),
          Function.Injective f → 0 < k → k < n → 0 < U → n ≤ k * U → 0 < m →
          (IsDoublingWith (Set.range p) D ∨ IsDoublingWith (Set.range f) D) →
          HaltsWithin prog [(n : ℤ), (m : ℤ), (k : ℤ), (U : ℤ)]
            ([z, ε, δ] ++ distanceList (instancePoints p f))
            ((C : ℝ) * ((n + m + 2 : ℕ) : ℝ) ^ C *
              (2 + Real.logb 2 (aspectRatio (instancePoints p f))) ^ C)
            (fun s => ∃ S : IdxSolution n m,
              IsSoftSolution (Set.range f) U (numOpenK k ε) (S.toSoft f) ∧
              ENNReal.ofReal ((S.toSoft f).cost z p) ≤
                ENNReal.ofReal ((3 : ℝ) ^ z - ((3 : ℝ) ^ z - 1) * ε + δ) *
                  opt z p (Set.range f) U k ∧
              OutputIs s S.encode [])) ∧
    (∀ D z ε δ : ℝ, 1 ≤ z → 0 < ε → ε ≤ 1 → 0 < δ →
      ∃ prog : Program, Admissible prog ∧ ∃ C : ℕ,
        ∀ (d n k U : ℕ) (p : Fin n → Euc d),
          0 < k → k < n → 0 < U → n ≤ k * U →
          IsDoublingWith (Set.range p) D →
          HaltsWithin prog [(n : ℤ), (d : ℤ), (k : ℤ), (U : ℤ)] ([z, ε, δ] ++ coordList p)
            ((C : ℝ) * ((d + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) ^ C *
              (2 + Real.logb 2 (aspectRatio p)) ^ C)
            (fun s => ∃ S : SoftSolution (Euc d) n,
              IsSoftSolution Set.univ U (numOpenK k ε) S ∧
              ENNReal.ofReal (S.cost z p) ≤
                ENNReal.ofReal (betaStar z - (betaStar z - 1) * ε + δ) * opt z p Set.univ U k ∧
              (0 < opt z p Set.univ U k → Function.Injective S.loc) ∧
              OutputIs s ((S.numCenters : ℤ) :: List.ofFn fun i => ((S.assign i : ℕ) : ℤ))
                (coordList S.loc))) := by sorry

end ChengCapClustering.Soft
