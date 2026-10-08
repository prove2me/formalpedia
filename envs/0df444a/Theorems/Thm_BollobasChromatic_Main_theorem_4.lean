-- Prove2me | Theorems.Thm_BollobasChromatic_Main_theorem_4
-- name    : BollobasChromatic.Main.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:09.877235+00:00
-- url     : https://prove2.me/theorems/ccde649a-659b-47bc-8e08-d41a9396e399
-- title:
--   Theorem 4, p. 52 — for fixed 0 < p < 1, a.e. G(n,p) has n/s₀ ≤ χ ≤ (n/s₀)(1 + 3 log log n/log n)
-- statement:
--   Let $0<p<1$ be fixed and set $q=1-p$, $d=1/q$ and
--   $$
--   s_0=\bigl[\,2\log_d n-\log_d\log_d n+2\log_d(e/2)+1\,\bigr],
--   $$
--   where $[x]$ is the integer part and $\log$ is the natural logarithm. Then almost every random graph $G_p=G_{n,p}$ satisfies
--   $$
--   \frac n{s_0}\le\chi(G_p)\le\frac n{s_0}\Bigl(1+\frac{3\log\log n}{\log n}\Bigr),
--   $$
--   that is, the probability that both inequalities hold tends to $1$ as $n\to\infty$.
--
--   This determines the chromatic number of the dense random graph asymptotically: $\chi(G_{n,p})=(1+o(1))\,n/(2\log_d n)$ almost surely, settling the factor-$2$ gap left by Grimmett and McDiarmid.
--
--   **Formalization Note** $\chi(G)$ is Mathlib's chromatic number, finite on a finite vertex set and converted to a natural number. Both bounds are required of the same graph. $p$ does not depend on $n$. For small $n$ the logarithms and $s_0$ take junk values; the statement is a limit and does not depend on them.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 52, Theorem 4

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem theorem_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    AlmostEvery p (fun n G =>
      (n : ℝ) / (s0 p n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) ∧
        (G.chromaticNumber.toNat : ℝ) ≤
          (n : ℝ) / (s0 p n : ℝ) * (1 + 3 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) := by sorry

end BollobasChromatic.Main
