-- Prove2me | Theorems.Thm_Avram2004_Exit_first_expectation
-- name    : Avram2004.Exit.first_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:23:59.206995+00:00
-- url     : https://prove2.me/theorems/1de13a32-da7f-4f64-b4de-ea12267dc09f
-- title:
--   Eqs. (14)–(15) — the first expectation of (13): exit of Y above k before hitting 0
-- statement:
--   In the setting of (13): $X$ spectrally negative Lévy satisfying the standing assumption, $Y$ the reflected process under $\mathbb P_{s,x}$ with $z=s-x\ge0$, $k>0$, $\psi(v)<\infty$, $u\ge\psi(v)\vee0$ and $p=u-\psi(v)$. Then $e^{-u\tau_k-vY_{\tau_k}}\mathbf 1_{\{\tau_k<\tau_{\{0\}}\}}$ is integrable and
--   $$\mathbb E_{s,x}\Big[e^{-u\tau_k-vY_{\tau_k}}\,\mathbf 1_{\{\tau_k<\tau_{\{0\}}\}}\Big]=e^{-vz}\Big(Z_v^{(p)}(k-z)-W_v^{(p)}(k-z)\,\frac{Z_v^{(p)}(k)}{W_v^{(p)}(k)}\Big).$$
--
--   The paper obtains this by identifying $Y$ before $\tau_{\{0\}}$ with $-X$ before $T_0^+$ (14), changing measure to the Esscher transform $\mathbb P^v$, and applying (10) under $\mathbb P^v$; the display (15) is the resulting identity under $\mathbb P^v_{-z}$, and the statement here is the claim that the page makes about $\mathbb P_{s,x}$.
--
--   **Formalization Note** The Esscher measure is not constructed: the statement is the composite "first expectation of (13) $=\exp(-vz)\times$ right side of (15)", which is what the proof uses. It holds for every $z\ge0$ (for $z\ge k$ both sides equal $e^{-vz}$, and for $z=0$ both sides vanish).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 221, proof of Theorem 1, Eqs. (14)–(15) and the sentence joining them

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

/-- (14)–(15), p. 221: the first expectation of (13). Under `u ≥ ψ(v) ∨ 0` and `ψ(v) < ∞`, with
`z = s - x ≥ 0` and `p = u - ψ(v)`,
`𝔼_{s,x}[e^{-uτ_k - vY_{τ_k}} I(τ_k < τ_{0})] = e^{-vz} (Z_v^{(p)}(k - z) - W_v^{(p)}(k - z) Z_v^{(p)}(k) / W_v^{(p)}(k))`. -/
theorem first_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (s x k u v : ℝ) (hxs : x ≤ s) (hk : 0 < k)
    (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) (hu0 : 0 ≤ u) (hu : Shared.psi P X v ≤ u) :
    Integrable (fun ω => if tau s x X k ω < tauZero s x X ω
      then exitFunctional s x X k u v ω else 0) P ∧
    ∫ ω, (if tau s x X k ω < tauZero s x X ω then exitFunctional s x X k u v ω else 0) ∂P
      = Real.exp (-v * (s - x)) *
        (Shared.Z P X v (u - Shared.psi P X v) (k - (s - x))
          - Shared.W P X v (u - Shared.psi P X v) (k - (s - x)) * Shared.Z P X v (u - Shared.psi P X v) k
            / Shared.W P X v (u - Shared.psi P X v) k) := by sorry

end Avram2004.Exit
