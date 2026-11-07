-- Prove2me | Theorems.Thm_AvgPHETH_theorem_1_1
-- name    : AvgPHETH.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:45.255654+00:00
-- url     : https://prove2.me/theorems/f4dd4689-2e30-410c-a472-5fb5488ac392
-- title:
--   Theorem 1.1 — $\mathrm{wETH}^{\mathrm{NP}}$ implies $\mathrm{Dist}\Sigma_2^p\not\subseteq\mathrm{AvgP}$
-- statement:
--   If $\Sigma_2\mathrm{SAT}$ on $N$ variables cannot be solved in time $2^{O(N/\log N)}\cdot\mathrm{poly}(n)$ by deterministic algorithms with an NP oracle, then
--
--   $$\mathrm{Dist}\Sigma_2^p\not\subseteq\mathrm{AvgP}.$$
--
--   That is, a worst-case hypothesis measured in the number of variables implies that some language in $\Sigma_2^p$ is hard on average, with respect to some polynomial-time samplable distribution, for errorless heuristic schemes. This is the main result of the paper.
--
--   Differences from the source:
--   - encoding: $2^{O(N/\log N)}\cdot\mathrm{poly}(n)$ → $\lceil2^{cN/\log_2\max(N,2)}(n+2)^c\rceil$ with one natural $c$; reason: two constants collapse to one by taking the larger; $\max(N,2)$ only excludes $N\le1$, where the logarithm is $0$
--   - encoding: an instance of input length $n$ on $N$ variables → Inst3DNF.enc, with the two numbers of variables in unary; reason: unused variables and repeated terms change nothing, and conversions take polynomial time
--   - reading: "3DNF" → terms of at most three literals; reason: with this reading $\mathrm{wETH}^{\mathrm{NP}}$ is the weaker hypothesis of the two readings, so the theorem is the stronger one
--   - encoding: NP and $\Sigma_2^p$ on the usual machine → SigmaPO ∅ 1 and SigmaPO ∅ 2 on the two-tape machine KarpLiptonOM.OracleTM, whose oracle $\emptyset$ answers "no"; reason: same classes up to polynomial overhead
--   - encoding: the output $\bot$ → any output string other than the two bits; reason: an errorless scheme can be converted between the two conventions
--   - encoding: a randomized polynomial-time sampler $S(1^n)$ → a deterministic machine on $(1^n,r)$ with $r$ uniform in $\{0,1\}^{r(n)}$, halting within $(n+r(n))^e+e$ steps (IsSampler); reason: the same class of polynomial-time samplable families
--   - encoding: running time $\mathrm{poly}(n,1/\delta)$ of the errorless scheme → $(n+\lceil1/\delta\rceil+2)^e+e$ steps on input $(x,1^n,1^{\lceil1/\delta\rceil})$; reason: every polynomial in $n$ and $1/\delta$ is bounded by one of this form
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_AvgPHETH_wETH_NP
import Definitions.Def_AvgPHETH_DistSubAvgP

namespace AvgPHETH

/-- **Theorem 1.1** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.2 (PDF 4)). `wETH^NP` implies `DistΣ₂^p ⊄ AvgP`.

**Formalization Note** `¬ DistSubAvgP ∅ 2` says that there are `L ∈ Σ₂^p` and a polynomial-time samplable family `D` with `(L, D) ∉ AvgP`. The oracle `∅` is the absence of an oracle: a machine
with oracle `∅` gets the answer "no" to every query. -/
theorem theorem_1_1 : wETH_NP → ¬ DistSubAvgP ∅ 2 := by sorry

end AvgPHETH
