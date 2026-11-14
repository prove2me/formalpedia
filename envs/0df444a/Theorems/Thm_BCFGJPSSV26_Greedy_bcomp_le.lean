-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_bcomp_le
-- name    : BCFGJPSSV26.Greedy.bcomp_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:23.134427+00:00
-- url     : https://prove2.me/theorems/b67b0c03-e12c-496b-932d-63d6b192d077
-- title:
--   Extra facilities of the trivial solution: $\lfloor\log_2 n\rfloor\lceil1/\delta^2\rceil\le10^{10}\log n/\varepsilon^2$
-- statement:
--   A bound on constants for Theorem 1.2 of Part I: the number of extra facilities that the algorithm allows to the trivial solution is at most $C\log n/\varepsilon^2$ with $C=10^{10}$.
--
--   **Statement.** Let $\varepsilon$ be a real number with $0<\varepsilon<4$. Let $\delta=\delta(\varepsilon)$ be the constant of the algorithm of Theorem 1.2: for $\varepsilon\le1$ a fixed rational number with $\tfrac{\varepsilon}{200}<\delta<\tfrac{\varepsilon}{100}$, and $\delta=\tfrac1{100}$ for $1<\varepsilon<4$. Then for every natural number $n$,
--
--   $$\lfloor\log_2n\rfloor\cdot\Bigl\lceil\frac1{\delta^2}\Bigr\rceil\ \le\ 10^{10}\cdot\frac{\ln n}{\varepsilon^2}.$$
--
--   The main algorithm outputs the trivial solution (the nearest facility of every client) whenever it has at most $k+\lfloor\log_2n\rfloor\lceil1/\delta^2\rceil$ facilities. By this bound the output then has at most $k+C\log n/\varepsilon^2$ facilities, with the same constant $C=10^{10}$ for all $\varepsilon$, as Theorem 1.2 requires. The companion bound $6R\le C\log n/\varepsilon^2$ covers the other case.
--
--   **Formalization Note** $\ln$ is the natural logarithm, with $\ln0=0$, and $\lfloor\log_20\rfloor=0$, so the inequality reads $0\le0$ for $n\le1$. For $\varepsilon\le1$ the number $\delta$ is obtained by choice from the existence of a rational in the interval.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2. Lean source: `BCFGJPSSV26.Greedy.bcomp_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Constants.lean#L116-L150

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

theorem bcomp_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) (n : ℕ) :
    (bcomp (constsOf ε) n : ℝ) ≤ Cthm * Real.log n / ε ^ 2 := by sorry

end BCFGJPSSV26.Greedy
end
