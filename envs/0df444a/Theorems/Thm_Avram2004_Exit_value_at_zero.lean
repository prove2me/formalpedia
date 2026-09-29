-- Prove2me | Theorems.Thm_Avram2004_Exit_value_at_zero
-- name    : Avram2004.Exit.value_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:25:05.054323+00:00
-- url     : https://prove2.me/theorems/2ebfa0db-f39d-4ace-822b-ca3a5cc04010
-- title:
--   Eq. (22) — the constant C = 𝔼_{0,0}[e^{−uτ_k−vY_{τ_k}}]
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$, and let $Y$ be the reflected process started at $0$ (under $\mathbb P_{0,0}$), with $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$, $k>0$. Let $v$ satisfy $\psi(v)<\infty$, let $u\ge\psi(v)\vee0$ and $p=u-\psi(v)$. Then $e^{-u\tau_k-vY_{\tau_k}}$ is integrable and
--   $$C=\mathbb E_{0,0}\big[e^{-u\tau_k-vY_{\tau_k}}\big]=-W_v^{(p)}(k)\,\frac{pW_v^{(p)}(k)+vZ_v^{(p)}(k)}{W_v^{(p)\prime}(k)+vW_v^{(p)}(k)}+Z_v^{(p)}(k).$$
--
--   This is the value of the reflected exit functional for $Y$ started at $0$; the paper computes it with the compensation formula of excursion theory, and substituting it with (15) and (16) into (13) gives Theorem 1 for $u\ge\psi(v)\vee0$.
--
--   **Formalization Note** $W_v^{(p)\prime}(k)$ is the derivative of $x\mapsto W_v^{(p)}(x)$ at $k>0$, which exists under the standing assumption. The paper derives (22) for unbounded variation and then treats bounded variation separately; the statement covers both, i.e. the whole standing assumption, which is what the paper has established at the end of the proof.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 224, proof of Theorem 1, Eq. (22)

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

/-- (22), p. 224: under `u ≥ ψ(v) ∨ 0` and `ψ(v) < ∞`, with `p = u - ψ(v)`, the constant
`C = 𝔼_{0,0}[e^{-uτ_k - vY_{τ_k}}]` of (13) equals
`-W_v^{(p)}(k) (pW_v^{(p)}(k) + vZ_v^{(p)}(k)) / (W_v^{(p)'}(k) + vW_v^{(p)}(k)) + Z_v^{(p)}(k)`. -/
theorem value_at_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (k u v : ℝ) (hk : 0 < k)
    (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) (hu0 : 0 ≤ u) (hu : Shared.psi P X v ≤ u) :
    Integrable (exitFunctional 0 0 X k u v) P ∧
    ∫ ω, exitFunctional 0 0 X k u v ω ∂P
      = -Shared.W P X v (u - Shared.psi P X v) k
          * ((u - Shared.psi P X v) * Shared.W P X v (u - Shared.psi P X v) k + v * Shared.Z P X v (u - Shared.psi P X v) k)
          / (deriv (Shared.W P X v (u - Shared.psi P X v)) k + v * Shared.W P X v (u - Shared.psi P X v) k)
        + Shared.Z P X v (u - Shared.psi P X v) k := by sorry

end Avram2004.Exit
