-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_sixR_le
-- name    : BCFGJPSSV26.Greedy.sixR_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:17.035928+00:00
-- url     : https://prove2.me/theorems/7f911bd3-e882-43b3-aa51-9b1cacfda54c
-- title:
--   Free copies of the core: $6R\le10^{10}\log n/\varepsilon^2$ when the trivial solution is too large
-- statement:
--   A bound on constants for Theorem 1.2 of Part I: when $n$ exceeds the number of extra facilities allowed to the trivial solution, the $6R$ free copies that the core of the log-adaptive greedy algorithm may open are at most $C\log n/\varepsilon^2$ with $C=10^{10}$.
--
--   **Statement.** Let $\varepsilon$ be a real number with $0<\varepsilon<4$. Let $\delta=\delta(\varepsilon)$ be the constant of the algorithm of Theorem 1.2: for $\varepsilon\le1$ a fixed rational number with $\tfrac{\varepsilon}{200}<\delta<\tfrac{\varepsilon}{100}$, and $\delta=\tfrac1{100}$ for $1<\varepsilon<4$. Let $\varepsilon_g=\tfrac{\delta}{10}$ and $\varepsilon'=25\delta$, and for a natural number $n$ let
--   $$M=\frac{8n^2}{\varepsilon'}+1,\qquad R=\Bigl\lceil\frac1{\varepsilon_g^2}\Bigr\rceil\cdot\bigl\lceil\log_2\lceil5nM\rceil\bigr\rceil+1 .$$
--   If $n\ge2$ and $\lfloor\log_2n\rfloor\cdot\lceil1/\delta^2\rceil<n$, then
--
--   $$6R\ \le\ 10^{10}\cdot\frac{\ln n}{\varepsilon^2}.$$
--
--   $R$ is the number of phases of the log-adaptive greedy algorithm after the distances are scaled into $[1,M]$, and the core outputs at most $k+6R$ facilities. The hypothesis $\lfloor\log_2n\rfloor\lceil1/\delta^2\rceil<n$ holds whenever the main algorithm does not output the trivial solution, and it keeps the bound uniform in $\varepsilon$, although after the scaling $\log M$ is only $O(\log n+\log(1/\varepsilon))$ in general. Together with the bound on the extra facilities of the trivial solution this gives the count $k+C\log n/\varepsilon^2$ of Theorem 1.2.
--
--   **Formalization Note** $\ln$ is the natural logarithm. For $1<\varepsilon<4$ the constants are $\delta=\tfrac1{100}$, $\varepsilon_g=\tfrac1{1000}$, $\varepsilon'=\tfrac14$; for $\varepsilon\le1$ the number $\delta$ is obtained by choice from the existence of a rational in the interval.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2. Lean source: `BCFGJPSSV26.Greedy.sixR_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Constants.lean#L215-L240

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

theorem sixR_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) {n : ℕ} (hbn : bcomp (constsOf ε) n < n)
    (hn : 2 ≤ n) : ((6 * Rof (constsOf ε) n : ℕ) : ℝ) ≤ Cthm * Real.log n / ε ^ 2 := by sorry

end BCFGJPSSV26.Greedy
end
