-- Prove2me | Theorems.Thm_Avram2004_Exit_remark6_martingale
-- name    : Avram2004.Exit.remark6_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:26:04.14795+00:00
-- url     : https://prove2.me/theorems/d1a1a531-48bc-41d6-84ec-02fe12c7522e
-- title:
--   Remark 6, Eq. (23) — the stopped reflected exit martingale
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, $Y$ the reflected process under $\mathbb P_{s,x}$ ($x\le s$), $k>0$ and $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$. Let $u\ge0$, let $v$ satisfy $\psi(v)<\infty$, and $p=u-\psi(v)$. Then the process
--   $$M_t=e^{-u(t\wedge\tau_k)-vY_{t\wedge\tau_k}}\left(Z_v^{(p)}(k-Y_{t\wedge\tau_k})-\frac{vZ_v^{(p)}(k)+pW_v^{(p)}(k)}{W_v^{(p)\prime}(k)+vW_v^{(p)}(k)}\,W_v^{(p)}(k-Y_{t\wedge\tau_k})\right),\qquad t\ge0,$$
--   is a martingale with respect to the natural filtration of $X$.
--
--   Its expectation at time $0$ and at time $\tau_k$ coincide, which is the content of Theorem 1; the martingale is the tool the paper uses in the bounded-variation case and again in the Russian option problem.
--
--   **Formalization Note** The page prints $vZ_v^{(q)}(k)$ in the numerator; no $q$ is in scope, and (12) and (22) have $vZ_v^{(p)}(k)$, so this is a misprint and the statement uses $Z_v^{(p)}$. The filtration is the natural filtration of $X$ ($\mathbb P_{s,x}$ is a deterministic shift of $X$). The martingale property includes adaptedness and integrability of each $M_t$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 225, Remark 6, Eq. (23)

import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Exit_passageTimes
import Definitions.Def_Avram2004_Exit_reflected

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- Remark 6, (23), p. 225: for `u ≥ 0` and `v` with `ψ(v) < ∞`, `k > 0`, `x ≤ s` and `p = u - ψ(v)`,
the process
`e^{-u(t∧τ_k) - vY_{t∧τ_k}} (Z_v^{(p)}(k - Y_{t∧τ_k}) - (vZ_v^{(p)}(k) + pW_v^{(p)}(k)) / (W_v^{(p)'}(k) + vW_v^{(p)}(k)) W_v^{(p)}(k - Y_{t∧τ_k}))`,
`t ≥ 0`, is a `ℙ_{s,x}`-martingale for the natural filtration of `X`. (The page prints `vZ_v^{(q)}(k)`,
a misprint for `vZ_v^{(p)}(k)`.) -/
theorem remark6_martingale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (s x k u v : ℝ) (hxs : x ≤ s) (hk : 0 < k) (hu : 0 ≤ u)
    (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) :
    Martingale
      (fun t ω =>
        Real.exp (-u * (stopAt t (tau s x X k ω) : ℝ)
            - v * refl s x X (stopAt t (tau s x X k ω)) ω)
          * (Shared.Z P X v (u - Shared.psi P X v) (k - refl s x X (stopAt t (tau s x X k ω)) ω)
            - (v * Shared.Z P X v (u - Shared.psi P X v) k + (u - Shared.psi P X v) * Shared.W P X v (u - Shared.psi P X v) k)
              / (deriv (Shared.W P X v (u - Shared.psi P X v)) k + v * Shared.W P X v (u - Shared.psi P X v) k)
              * Shared.W P X v (u - Shared.psi P X v) (k - refl s x X (stopAt t (tau s x X k ω)) ω)))
      (Filtration.natural X (fun t => (hX.measurable t).stronglyMeasurable)) P := by sorry

end Avram2004.Exit
