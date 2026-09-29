-- Prove2me | Theorems.Thm_Avram2004_Exit_decomposition_at_zero
-- name    : Avram2004.Exit.decomposition_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:23:27.832098+00:00
-- url     : https://prove2.me/theorems/38bbeb6e-39df-4a9b-8ffc-4c95f913d33d
-- title:
--   Eq. (13) — splitting 𝔼_{s,x}[e^{−uτ_k−vY_{τ_k}}] at the first zero τ_{0} of Y
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$, and let $Y=\overline X-X$ be the reflected process under $\mathbb P_{s,x}$ ($x\le s$), with $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$ for $k>0$ and $\tau_{\{0\}}=\inf\{t\ge0:Y_t=0\}$. Let $v$ satisfy $\psi(v)<\infty$ and let $u\ge\psi(v)\vee0$. Then all expectations below are finite, the constant
--   $$C=\mathbb E_{s,s}\big[e^{-u\tau_k-vY_{\tau_k}}\big]=\mathbb E_{0,0}\big[e^{-u\tau_k-vY_{\tau_k}}\big]$$
--   does not depend on $s$, and
--   $$\mathbb E_{s,x}\big[e^{-u\tau_k-vY_{\tau_k}}\big]=\mathbb E_{s,x}\big[e^{-u\tau_k-vY_{\tau_k}}\mathbf 1_{\{\tau_k<\tau_{\{0\}}\}}\big]+C\,\mathbb E_{s,x}\big[e^{-u\tau_{\{0\}}}\mathbf 1_{\{\tau_k>\tau_{\{0\}}\}}\big].$$
--
--   This is the first step of the proof of Theorem 1: the strong Markov property of $Y$ at its first zero reduces the problem to $Y$ started at $0$.
--
--   **Formalization Note** The functional $e^{-u\tau_k-vY_{\tau_k}}$ is set to $0$ on $\{\tau_k=\infty\}$. The restriction $u\ge\psi(v)\vee0$ is the one under which the paper writes (13) ("Suppose first that $u,v$ are such that $u\ge\psi(v)\vee0$").
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 221, proof of Theorem 1, Eq. (13)

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

/-- (13), p. 221: under `u ≥ ψ(v) ∨ 0` and `ψ(v) < ∞`, the strong Markov property of `Y` at `τ_{0}`
splits the joint Laplace transform:
`𝔼_{s,x}[e^{-uτ_k - vY_{τ_k}}] = 𝔼_{s,x}[e^{-uτ_k - vY_{τ_k}} I(τ_k < τ_{0})] + C 𝔼_{s,x}[e^{-uτ_{0}} I(τ_k > τ_{0})]`,
where `C = 𝔼_{s,s}[e^{-uτ_k - vY_{τ_k}}] = 𝔼_{0,0}[e^{-uτ_k - vY_{τ_k}}]`. -/
theorem decomposition_at_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (s x k u v : ℝ) (hxs : x ≤ s) (hk : 0 < k)
    (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) (hu0 : 0 ≤ u) (hu : Shared.psi P X v ≤ u) :
    Integrable (exitFunctional s x X k u v) P ∧
    Integrable (fun ω => if tau s x X k ω < tauZero s x X ω
      then exitFunctional s x X k u v ω else 0) P ∧
    Integrable (fun ω => if tauZero s x X ω < tau s x X k ω
      then discount u (tauZero s x X ω) else 0) P ∧
    Integrable (exitFunctional s s X k u v) P ∧
    Integrable (exitFunctional 0 0 X k u v) P ∧
    ∫ ω, exitFunctional s s X k u v ω ∂P = ∫ ω, exitFunctional 0 0 X k u v ω ∂P ∧
    ∫ ω, exitFunctional s x X k u v ω ∂P =
      (∫ ω, (if tau s x X k ω < tauZero s x X ω then exitFunctional s x X k u v ω else 0) ∂P)
      + (∫ ω, exitFunctional s s X k u v ω ∂P) *
        ∫ ω, (if tauZero s x X ω < tau s x X k ω then discount u (tauZero s x X ω) else 0) ∂P := by sorry

end Avram2004.Exit
