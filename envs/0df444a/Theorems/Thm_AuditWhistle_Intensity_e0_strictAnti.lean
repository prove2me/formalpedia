-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_e0_strictAnti
-- name    : AuditWhistle.Intensity.e0_strictAnti
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:31.091715+00:00
-- url     : https://prove2.me/theorems/58a930b5-6a23-448a-81a8-d124841b6bde
-- title:
--   Appendix, proof of Proposition 2, (27), p. 32 — the equilibrium effort after silence e₀* decreases in τ
-- statement:
--   Fix a model and two intensities $0<\tau<\tau'<1$. If $(a,e_1,e_0)$ is an equilibrium at $\tau$ and $(a',e_1',e_0')$ is an equilibrium at $\tau'$, then
--   $$e_0'<e_0.$$
--
--   This is the "silence effect": the more intense whistleblowing is, the more reassuring silence becomes, so the enforcer investigates less when there is no tip. In the paper it is the conclusion $de_0^*/d\tau<0$ of the implicit function theorem applied to (27).
--
--   **Formalization Note** The derivative statement is formalized as strict monotonicity of the equilibrium value, because $e_0^*$ need not be differentiable in $\tau$ where the equilibrium crosses the kink of $e_1=\min\{1,\cdot\}$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 32, Appendix, proof of Proposition 2, (27)

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

namespace AuditWhistle.Intensity

theorem e0_strictAnti (M : Model) (τ τ' a e1 e0 a' e1' e0' : ℝ)
    (hτ : τ ∈ Set.Ioo (0:ℝ) 1) (hτ' : τ' ∈ Set.Ioo (0:ℝ) 1) (hlt : τ < τ')
    (h : IsEquilibrium M τ a e1 e0) (h' : IsEquilibrium M τ' a' e1' e0') :
    e0' < e0 := by sorry

end AuditWhistle.Intensity
