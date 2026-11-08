-- Prove2me | Theorems.Thm_BeatingGV42_sec_4_5_identities
-- name    : BeatingGV42.sec_4_5_identities
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:33:41.6702+00:00
-- url     : https://prove2.me/theorems/487b1a24-3425-4d17-ba4b-d1c67efceef0
-- title:
--   §4.5 identities — $R(a_{GV}(\delta))=1-H_{42}(\delta)$, $\Psi_{a_{GV}(\delta),42}(1/49,\delta)=0$, and $\partial_t\Psi|_{t=1/49}=\frac{49}{\ln49}F(\delta)$
-- statement:
--   With $Q=49$, $q=42$, $h(x)=-x\ln x-(1-x)\ln(1-x)$, $a_{GV}(\delta)=\frac76-\frac{h(\delta)+\delta\ln41}{\ln49}$ and $F(\delta)=h(\delta)+\delta\ln41-\frac{49\delta+7}{48}\ln49$, for every $\delta\in(0,1)$:
--
--   1. $R(a_{GV}(\delta))=1-H_{42}(\delta)$;
--   2. for every real $a$, $\Psi_{a,42}(1/49,\delta)=h(\delta)+\delta\ln41-\bigl(\tfrac76-a\bigr)\ln49$;
--   3. $\Psi_{a_{GV}(\delta),42}(1/49,\delta)=0$;
--   4. $t\mapsto\Psi_{a_{GV}(\delta),42}(t,\delta)$ is differentiable at $t=1/49$ with derivative $49\bigl(\tfrac{49}{48}(1-\delta)-a_{GV}(\delta)\bigr)$, and this equals $\frac{49}{\ln49}F(\delta)$.
--
--   At the GV-matching degree the exponent vanishes at the boundary point $t=1/49$, and its slope there is a positive multiple of $F(\delta)$.
--
--   **Formalization Note** $R$ is `rateR 49 42`, $\Psi$ is `Psi 49 42`, $h$ is `Real.binEntropy`, $F$ is `Fgap`; the derivative is a `HasDerivAt` in $t$.
--
--   Differences from the source:
--   - generalization: δ ∈ I = [0.39, 0.48] → δ ∈ (0, 1); reason: the identities hold on (0, 1) and specialize to I
--   - encoding: ∂/∂t Ψ_{a_GV(δ),42}(t, δ)|_{t=1/49} = 49((49/48)(1 − δ) − a_GV(δ)) = (49/ln 49) F(δ) → HasDerivAt (fun t => Psi 49 42 (aGV δ) t δ) (49 * (49/48 * (1 − δ) − aGV δ)) (1/49) ∧ 49 * (49/48 * (1 − δ) − aGV δ) = 49 / log 49 * Fgap δ; reason: the derivative and both printed forms of its value
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.5, pp.23–24 (PDF pp.25–26)

import Mathlib
import Definitions.Def_BeatingGV42_Hq
import Definitions.Def_BeatingGV42_Psi
import Definitions.Def_BeatingGV42_rateR
import Definitions.Def_BeatingGV42_aGV
import Definitions.Def_BeatingGV42_Fgap

set_option autoImplicit false

namespace BeatingGV42

/-- **The §4.5 identities** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.5, pp.23–24 (PDF pp.25–26)), with `Q = 49`, `q = 42`:
1. "R(a_GV(δ)) = 1 − H_42(δ)";
2. "Ψ_{a,42}(1/49, δ) = h(δ) + δ ln 41 − (7/6 − a) ln 49" for every `a`;
3. "Ψ_{a_GV(δ),42}(1/49, δ) = 0";
4. "∂/∂t Ψ_{a_GV(δ),42}(t, δ)|_{t=1/49} = 49((49/48)(1 − δ) − a_GV(δ)) = (49/ln 49) F(δ)".

**Formalization Note** Stated for every `δ ∈ (0, 1)` (the page has `δ ∈ I = [0.39, 0.48]`; the
identities hold on `(0, 1)`). `R(a) = rateR 49 42 a` (`1 + 1/(√49 − 1) = 7/6`), `h = Real.binEntropy`,
`F = Fgap`. The derivative is a `HasDerivAt` in `t` at `t = 1/49`, with both printed forms of its
value. -/
theorem sec_4_5_identities (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    rateR 49 42 (aGV δ) = 1 - Hq 42 δ ∧
    (∀ a : ℝ, Psi 49 42 a (1 / 49) δ =
      Real.binEntropy δ + δ * Real.log 41 - (7 / 6 - a) * Real.log 49) ∧
    Psi 49 42 (aGV δ) (1 / 49) δ = 0 ∧
    HasDerivAt (fun t => Psi 49 42 (aGV δ) t δ) (49 * (49 / 48 * (1 - δ) - aGV δ)) (1 / 49) ∧
    49 * (49 / 48 * (1 - δ) - aGV δ) = 49 / Real.log 49 * Fgap δ := by sorry

end BeatingGV42
