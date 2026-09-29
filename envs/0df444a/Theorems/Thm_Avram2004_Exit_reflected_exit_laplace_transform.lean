-- Prove2me | Theorems.Thm_Avram2004_Exit_reflected_exit_laplace_transform
-- name    : Avram2004.Exit.reflected_exit_laplace_transform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:25:34.598262+00:00
-- url     : https://prove2.me/theorems/620b9b2e-66da-4e68-8873-6ea2dba0d78b
-- title:
--   Theorem 1 — joint Laplace transform of τ_k and Y_{τ_k} for the reflected process Y = X̄ − X
-- statement:
--   Let $X$ be a spectrally negative Lévy process with Laplace exponent $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$, satisfying the standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Under $\mathbb P_{s,x}$ the process starts at $x$ with prior maximum $s\ge x$; let $\overline X_t=\max\{s,\sup_{0\le u\le t}X_u\}$, $Y=\overline X-X$, and for $k>0$
--   $$\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}.$$
--   Let $u\ge0$, let $v$ be real with $\psi(v)<\infty$, and put $z=s-x\ge0$ and $p=u-\psi(v)$. Then $e^{-u\tau_k-vY_{\tau_k}}$ is integrable and
--   $$\mathbb E_{s,x}\big[e^{-u\tau_k-vY_{\tau_k}}\big]=e^{-vz}\left(Z_v^{(p)}(k-z)-W_v^{(p)}(k-z)\,\frac{pW_v^{(p)}(k)+vZ_v^{(p)}(k)}{W_v^{(p)\prime}(k)+vW_v^{(p)}(k)}\right),$$
--   where $W_v^{(p)}$ and $Z_v^{(p)}$ are the scale functions of the tilted exponent $\psi_v(\theta)=\psi(\theta+v)-\psi(v)$ (Definition 2 when $p\ge0$, the series (5) when $p<0$).
--
--   This is the main result of the first half of the paper. With $v=0$ it gives the Laplace transform of the exit time of the reflected process from $[0,k)$; the full joint transform is what the paper uses to solve the Russian and Canadized Russian optimal stopping problems.
--
--   **Formalization Note** $v$ ranges over every real number with $e^{vX_1}$ integrable, including $v<0$, so $p$ may be negative. The case $z\ge k$ is allowed (then $\tau_k=0$ and both sides equal $e^{-vz}$), and so is $u=0$. The functional is given the value $0$ on $\{\tau_k=\infty\}$, an event of probability zero. Integrability is part of the conclusion: for $v<0$ the integrand is unbounded. $\mathbb P_{s,x}$ is encoded by the path $t\mapsto x+X_t$ together with the prior maximum $s$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, pp. 220–221, Theorem 1, Eq. (12)

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

/-- Theorem 1, (12), pp. 220–221: for `u ≥ 0` and `v` with `ψ(v) < ∞`, `k > 0`, `z = s - x ≥ 0` and
`p = u - ψ(v)`, the joint Laplace transform of `τ_k` and `Y_{τ_k}` under `ℙ_{s,x}` is
`𝔼_{s,x}[e^{-uτ_k - vY_{τ_k}}] = e^{-vz} (Z_v^{(p)}(k - z) - W_v^{(p)}(k - z) (pW_v^{(p)}(k) + vZ_v^{(p)}(k)) / (W_v^{(p)'}(k) + vW_v^{(p)}(k)))`. -/
theorem reflected_exit_laplace_transform {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (s x k u v : ℝ) (hxs : x ≤ s) (hk : 0 < k) (hu : 0 ≤ u)
    (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) :
    Integrable (exitFunctional s x X k u v) P ∧
    ∫ ω, exitFunctional s x X k u v ω ∂P
      = Real.exp (-v * (s - x)) *
        (Shared.Z P X v (u - Shared.psi P X v) (k - (s - x))
          - Shared.W P X v (u - Shared.psi P X v) (k - (s - x))
            * ((u - Shared.psi P X v) * Shared.W P X v (u - Shared.psi P X v) k + v * Shared.Z P X v (u - Shared.psi P X v) k)
            / (deriv (Shared.W P X v (u - Shared.psi P X v)) k + v * Shared.W P X v (u - Shared.psi P X v) k)) := by sorry

end Avram2004.Exit
