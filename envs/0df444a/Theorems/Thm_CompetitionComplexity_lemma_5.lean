-- Prove2me | Theorems.Thm_CompetitionComplexity_lemma_5
-- name    : CompetitionComplexity.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:43.75403+00:00
-- url     : https://prove2.me/theorems/c0dfcb75-104a-471d-92fd-f92e398938a2
-- title:
--   Lemma 5 — the recursion (9) versus the differential equation (15)–(16), and $\phi(\varepsilon)=\Theta(\log\log 1/\varepsilon)$
-- statement:
--   Let $\varepsilon>0$. The differential equation $y'(t)=y(t)(\log y(t)-1)-\varepsilon$ on $(0,\phi(\varepsilon))$, $y(0)=1$, has a unique solution $y_\varepsilon$ (on $[0,\phi(\varepsilon)]$, extended continuously at $\phi(\varepsilon)$). Furthermore:
--
--   1. **(a)** $y_\varepsilon'(t)<0$ for every $t\in[0,\phi(\varepsilon))$; $y_\varepsilon$ is strictly decreasing on $[0,\phi(\varepsilon))$, maps it bijectively onto $(0,1]$, and $y_\varepsilon(\phi(\varepsilon))=0$.
--   2. **(b)** For every integer $n\ge2$ and every $j$ for which $\rho_{\varepsilon,j}$ of the recursion (9) is well defined and $j/n\le\phi(\varepsilon)$,
--   $$
--   \frac{n-1}{n}\rho_{\varepsilon,j}^{\,n}-\frac{\varepsilon}{n}\le y_\varepsilon\Bigl(\frac jn\Bigr).
--   $$
--   3. **(c)** For every $\delta\in(0,\phi(\varepsilon))$ there is $n_0$ such that for every $n\ge n_0$, with $k=\lfloor(\phi(\varepsilon)-\delta)n\rfloor$, the term $\rho_{\varepsilon,k}$ is well defined and
--   $$
--   (n-1)\rho_{\varepsilon,k}^{\,n}-\varepsilon>0 .
--   $$
--   4. **(d)** $\phi(\varepsilon)=\Theta(\log\log 1/\varepsilon)$ as $\varepsilon\to0^+$.
--
--   Part (b) gives the sufficiency half of Theorem 2 (the recursion dies out by step $\phi(\varepsilon)n$), part (c) the tightness half, and part (d) the growth of the threshold.
--
--   Differences from the source:
--   - encoding: a solution of (15)–(16) on (0, ϕ(ε)) with continuous extension at ϕ(ε) → IsSol: continuous on [0, ϕ(ε)], y(0) = 1, y(t) > 0 and y′(t) = y(t)(log y(t) − 1) − ε on (0, ϕ(ε)); reason: the real logarithm in (15) requires y(t) > 0, which Lean's log |y| would not enforce
--   - encoding: a unique solution yε → existence, and any two solutions agree on [0, ϕ(ε)]; reason: a solution is only defined on [0, ϕ(ε)]; values elsewhere are unconstrained
--   - encoding: y′ε(t) < 0 for t ∈ [0, ϕ(ε)) → at t = 0 a right derivative exists and is negative; on (0, ϕ(ε)) the derivative is negative; reason: y is not defined left of 0, so y′(0) is the one-sided derivative
--   - encoding: yε is decreasing and invertible on [0, ϕ(ε)) → StrictAntiOn on [0, ϕ(ε)) and a bijection of [0, ϕ(ε)) onto (0, 1]; reason: "decreasing" is strict (y′ < 0) and (0, 1] is the image
--   - encoding: (b) for every j for which ρε,j is well defined → for every such j with j/n ≤ ϕ(ε); reason: yε(j/n) is defined only for j/n ≤ ϕ(ε) (the solution lives on [0, ϕ(ε)]); the proof of Theorem 2 uses (b) at j/n = ϕ(ε′)
--   - encoding: (c) (n − 1)ρⁿ_{ε,k} − ε > 0 → ρ_{ε,k} is well defined and (n − 1)ρⁿ_{ε,k} − ε > 0; reason: the expression presupposes that ρ_{ε,k} is well defined
--   - encoding: ϕ(ε) = Θ(log log 1/ε) → Asymptotics.IsTheta (𝓝[>] 0) ϕ (ε ↦ log(log(1/ε))); reason: the Θ relation of the source, as ε → 0⁺
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Lemma 5, pp.21–22

import Mathlib
import Definitions.Def_CompetitionComplexity_Phi
import Definitions.Def_CompetitionComplexity_Recursion
import Definitions.Def_CompetitionComplexity_ODE

open Filter Topology

namespace CompetitionComplexity

/-- **Lemma 5** (the recursion versus the differential equation).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Lemma 5, pp.21–22:
"For every ε > 0, the differential equation (15)-(16) has a unique solution yε. Furthermore, the
following holds:
(a) For every t ∈ [0,ϕ(ε)) we have y′ε(t) < 0. In particular, yε is decreasing and invertible on
[0,ϕ(ε)) and yε(ϕ(ε)) = 0.
(b) For every integer n ≥ 2, and every j ∈ N for which ρε,j is well-defined, we have
(n−1)/n ρ^n_{ε,j} − ε/n ≤ yε(j/n).
(c) For every δ ∈ (0,ϕ(ε)), there exists n0 such that for every n ≥ n0 we have (n − 1)ρ^n_{ε,k} − ε > 0,
where k = ⌊(ϕ(ε) − δ)n⌋.
(d) We have ϕ(ε) = Θ(log log 1/ε)."

**Formalization Note.** Solutions are compared on `[0, ϕ(ε)]`, where they are defined; `y′(0)` is the
right derivative. "Invertible on `[0, ϕ(ε))`" is a bijection onto `(0, 1]`. In (b), `yε(j/n)` is
defined only for `j/n ≤ ϕ(ε)`, so (b) is stated for those `j`. In (c), "(n − 1)ρⁿ_{ε,k} − ε > 0"
presupposes that `ρ_{ε,k}` is well defined, and both are concluded. (d) is
`ϕ(ε) = Θ(log log(1/ε))` as `ε → 0⁺`. -/
theorem lemma_5 (ε : ℝ) (hε : 0 < ε) :
    (∃ y : ℝ → ℝ, IsSol ε y) ∧
    (∀ y z : ℝ → ℝ, IsSol ε y → IsSol ε z → Set.EqOn y z (Set.Icc 0 (phi ε))) ∧
    (∀ y : ℝ → ℝ, IsSol ε y →
      (∃ d : ℝ, d < 0 ∧ HasDerivWithinAt y d (Set.Ici 0) 0) ∧
      (∀ t ∈ Set.Ioo 0 (phi ε), deriv y t < 0) ∧
      StrictAntiOn y (Set.Ico 0 (phi ε)) ∧
      Set.BijOn y (Set.Ico 0 (phi ε)) (Set.Ioc 0 1) ∧
      y (phi ε) = 0) ∧
    (∀ y : ℝ → ℝ, IsSol ε y → ∀ n : ℕ, 2 ≤ n → ∀ j : ℕ, WellDef ε n j →
      (j : ℝ) / n ≤ phi ε →
      ((n : ℝ) - 1) / n * rho ε n j ^ n - ε / n ≤ y ((j : ℝ) / n)) ∧
    (∀ δ ∈ Set.Ioo 0 (phi ε), ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      WellDef ε n ⌊(phi ε - δ) * n⌋₊ ∧
        0 < ((n : ℝ) - 1) * rho ε n ⌊(phi ε - δ) * n⌋₊ ^ n - ε) ∧
    Asymptotics.IsTheta (𝓝[>] (0 : ℝ)) phi (fun e => Real.log (Real.log (1 / e))) := by sorry

end CompetitionComplexity
