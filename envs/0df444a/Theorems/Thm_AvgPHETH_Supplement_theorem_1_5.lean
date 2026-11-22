-- Prove2me | Theorems.Thm_AvgPHETH_Supplement_theorem_1_5
-- name    : AvgPHETH.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:02:48.487065+00:00
-- url     : https://prove2.me/theorems/2ddba08d-3d3c-4631-8ac3-ed79d056f606
-- title:
--   Theorem 1.5 — an oracle with $\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O$ and $\Pi_k^{p,O}\not\subseteq\Sigma_k\mathrm{TIME}^O[2^{\varepsilon(n)n/\log^kn}]$
-- statement:
--   Let $\varepsilon:\mathbb N\to\mathbb R$ be an efficiently computable function with $\varepsilon(n)>0$ and $\varepsilon(n)=o(1)$. Then there exists an oracle $O$ such that $\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O$ and, for all $k\ge1$,
--
--   $$\Pi_k^{p,O}\not\subseteq\Sigma_k\mathrm{TIME}^O\Big[2^{\varepsilon(n)\cdot\frac{n}{\log^kn}}\Big].$$
--
--   So the bounds of Theorem 1.2 are optimal among relativizing techniques at every level of the polynomial hierarchy. Relative to $O$ the polynomial hierarchy does not collapse while $\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O$. Hence relativizing techniques cannot derive $\mathrm{DistPH}\not\subseteq\mathrm{AvgP}$ from the non-collapse of PH.
--
--   Differences from the source:
--   - reading: "efficiently computable" (not defined) → IsEfficientlyComputable: $g(n)=\max\{16,\lceil\log_2(1/\varepsilon(n))\rceil\}$ is computable from $1^n$ in time $n^e+e$; reason: the construction of §8.1 uses $\varepsilon$ only through $g(n)$; every standard reading implies this one, so the theorem is at least as strong
--   - reading: $\varepsilon(n)=o(1)$ with $\log(1/\varepsilon(n))$ used in §8.1 → $\varepsilon(n)>0$ for every $n$; reason: the parameter $g(n)$ on p.39 takes $\log(1/\varepsilon(n))$, which presupposes $\varepsilon(n)>0$
--   - encoding: $\varepsilon(n)=o(1)$ → Tendsto ε atTop (𝓝 0); reason: definition of $o(1)$
--   - reading: $\Sigma_k\mathrm{TIME}^O[t]$ for a bound $t$ that need not be time-constructible → SigmaKTime: $L(x)=\Phi^O_{T,W}(x)$ for all $T,W\ge\lceil c\,t(|x|)\rceil+c$, for some $c\ge1$ and machine $M$; reason: this is the characterisation of Definition 4.3 (p.15), which contains the page's class for time-constructible $t$; a larger class makes the non-inclusion at least as strong
--   - encoding: $\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O$ and $\Pi_k^{p,O}$ → $\forall d$, DistSubAvgP O d (published) and PiPO O k (complements of the published SigmaPO O k); reason: $\mathrm{DistPH}=\bigcup_d\mathrm{Dist}\Sigma_d^p$ (§4.1)
--   - encoding: $\log n$ → $\log_2 n$; at $n\le1$ the bound is $2^0=1$ (Lean's $x/0=0$); reason: two input lengths, absorbed by the threshold $\lceil c\,t\rceil+c$
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.5, p.4 (PDF 6); §8, pp.38–39 (PDF 40–41)

import Mathlib
import Definitions.Def_AvgPHETH_DistSubAvgP
import Definitions.Def_AvgPHETH_Supplement_PiPO
import Definitions.Def_AvgPHETH_Supplement_SigmaKTime
import Definitions.Def_AvgPHETH_Supplement_IsEfficientlyComputable

namespace AvgPHETH.Supplement

open AvgPHETH Filter Topology

/-- **Theorem 1.5** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.4 (PDF 6)): for every efficiently computable function `ε(n) = o(1)`,
there exists an oracle `O` such that `DistPH^O ⊆ AvgP^O` and, for all `k ≥ 1`,
`Π_k^{p,O} ⊄ Σ_kTIME^O[2^{ε(n)·(n/log^k n)}]`.

**Formalization Note** `DistPH^O ⊆ AvgP^O` is `DistΣ_d^{p,O} ⊆ AvgP^O` for every `d` (published
`AvgPHETH.DistSubAvgP`). `ε(n) > 0` is presupposed by `log(1/ε(n))` in §8.1; "efficiently computable"
is `IsEfficientlyComputable`. `log` is `log₂`; at `n ≤ 1`, `log₂ n = 0` and Lean's `x/0 = 0` makes the
bound `1` at those two lengths, which `SigmaKTime`'s threshold `⌈c·t⌉₊ + c` absorbs. The one oracle
`O` works for every `k`. -/
theorem theorem_1_5 (ε : ℕ → ℝ) (hpos : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hε : IsEfficientlyComputable ε) :
    ∃ O : Set (List Bool), (∀ d, DistSubAvgP O d) ∧
      ∀ k, 1 ≤ k → ∃ L ∈ PiPO O k,
        L ∉ SigmaKTime O k (fun n => (2 : ℝ) ^ (ε n * ((n : ℝ) / Real.logb 2 n ^ k))) := by sorry

end AvgPHETH.Supplement
