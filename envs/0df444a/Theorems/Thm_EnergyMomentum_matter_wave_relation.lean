-- Prove2me | Theorems.Thm_EnergyMomentum_matter_wave_relation
-- name    : EnergyMomentum.matter_wave_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:16:59.150066+00:00
-- url     : https://prove2.me/theorems/d010016a-66ee-4564-9199-ef9bb28b8dde
-- title:
--   Matter-wave form (3): $(\omega/c)^2 = k^2 + (mc/\hbar)^2$
-- statement:
--   Let $c>0$, $m>0$, $\hbar>0$ and $\mathbf v\in\mathbb R^3$ with $|\mathbf v|<c$, and let $E$ and $\mathbf p$ be the energy and momentum of the body. Suppose the de Broglie relations $E = \hbar\omega$ and $\mathbf p = \hbar\mathbf k$ hold for an angular frequency $\omega\in\mathbb R$ and a wavevector $\mathbf k\in\mathbb R^3$. Then, with $k = |\mathbf k|$,
--
--   $$
--   \left(\frac{\omega}{c}\right)^2 = k^2 + \left(\frac{mc}{\hbar}\right)^2 .
--   $$
--
--   This is the energy–momentum relation (1) expressed in terms of wave quantities.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Relation to quantum theory → Matter waves, equation (3).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Matter-wave form (3): with `E = ħ ω` and `𝐩 = ħ 𝐤`, `(ω / c)² = k² + (m c / ħ)²`. -/
theorem matter_wave_relation (m c hbar ω : ℝ) (v k : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) (hhbar : 0 < hbar)
    (hE : energy m c v = hbar * ω) (hp : momentum m c v = hbar • k) :
    (ω / c) ^ 2 = ‖k‖ ^ 2 + (m * c / hbar) ^ 2 := by sorry

end EnergyMomentum
