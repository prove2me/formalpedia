-- Prove2me | Theorems.Thm_Avram2004_Exit_second_expectation
-- name    : Avram2004.Exit.second_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:24:29.039804+00:00
-- url     : https://prove2.me/theorems/4eb36be7-892d-41dd-9ea3-a3ec47dd1551
-- title:
--   Eq. (16) — 𝔼_{−z}[e^{−uT_0^+}; T_{−k}^− > T_0^+] = W^(u)(k−z)/W^(u)(k) = e^{−vz}W_v^(p)(k−z)/W_v^(p)(k)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$, and let $\mathbb E_{-z}$ denote expectation for the process started at $-z$. Let $0<z<k$, let $v$ satisfy $\psi(v)<\infty$, let $u\ge\psi(v)\vee0$ and $p=u-\psi(v)$. Then $e^{-uT_0^+}\mathbf 1_{\{T_{-k}^->T_0^+\}}$ is integrable and
--   $$\mathbb E_{-z}\Big[e^{-uT_0^+}\,\mathbf 1_{\{T_{-k}^->T_0^+\}}\Big]=\frac{W^{(u)}(k-z)}{W^{(u)}(k)}=e^{-vz}\,\frac{W_v^{(p)}(k-z)}{W_v^{(p)}(k)} .$$
--
--   Via the identification (14) this is the second expectation of (13), the probability-weighted discount of $Y$ returning to $0$ before exceeding $k$; the first equality is (9) with $a=-k$, $b=0$, the second is Remark 4.
--
--   **Formalization Note** The range $0<z<k$ is that of Proposition 1, which needs the starting point $-z$ strictly inside $(-k,0)$. Both equalities are part of the claim.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 221, proof of Theorem 1, Eq. (16)

import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Exit_passageTimes

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- (16), p. 221: for `0 < z < k`, `u ≥ ψ(v) ∨ 0`, `ψ(v) < ∞` and `p = u - ψ(v)`, with `X` started at `-z`,
`𝔼_{-z}[e^{-uT_0^+} I(T_{-k}^- > T_0^+)] = W^{(u)}(k - z) / W^{(u)}(k) = e^{-vz} W_v^{(p)}(k - z) / W_v^{(p)}(k)`. -/
theorem second_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (z k u v : ℝ) (hz : 0 < z) (hzk : z < k)
    (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) (hu0 : 0 ≤ u) (hu : Shared.psi P X v ≤ u) :
    Integrable (fun ω => if Tplus (-z) X 0 ω < Tminus (-z) X (-k) ω
      then discount u (Tplus (-z) X 0 ω) else 0) P ∧
    ∫ ω, (if Tplus (-z) X 0 ω < Tminus (-z) X (-k) ω then discount u (Tplus (-z) X 0 ω) else 0) ∂P
      = Shared.W P X 0 u (k - z) / Shared.W P X 0 u k ∧
    Shared.W P X 0 u (k - z) / Shared.W P X 0 u k
      = Real.exp (-v * z) * (Shared.W P X v (u - Shared.psi P X v) (k - z) / Shared.W P X v (u - Shared.psi P X v) k) := by sorry

end Avram2004.Exit
