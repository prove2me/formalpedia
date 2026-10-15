-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_137
-- name    : DQI.Semicircle.eq_137
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:23.271195+00:00
-- url     : https://prove2.me/theorems/82fa7598-24db-4a8d-8cd2-9062e62f8a08
-- title:
--   (136)–(137), p. 34 — ρ + √(ρ(1 − ρ))(μd + 2√(μ(1 − μ))) = (√(μ(1 − ρ)) + √(ρ(1 − μ)))² for d = (1 − 2ρ)/√(ρ(1 − ρ))
-- statement:
--   Let $0<\rho<1$ and $0\le\mu\le1$, and put $d=(1-2\rho)/\sqrt{\rho(1-\rho)}$. Then
--   $$\rho+\sqrt{\rho(1-\rho)}\Big(\mu d+2\sqrt{\mu(1-\mu)}\Big)=\mu+\rho-2\mu\rho+2\sqrt{\mu(1-\mu)\rho(1-\rho)}=\Big(\sqrt{\mu(1-\rho)}+\sqrt{\rho(1-\mu)}\Big)^2 .$$
--
--   Combined with (131) and Lemma 9.3, this gives the closed form (9) of Theorem 4.1.
--
--   **Formalization Note** The identity holds for all such $\rho,\mu$; the page states it "for $\rho\le1-\mu$" only because the limit it is applied to is computed in that case.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 34, §9.4, (136)–(137)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (136)–(137), p. 34: `ρ + √(ρ(1−ρ))(μd + 2√(μ(1−μ))) = (√(μ(1−ρ)) + √(ρ(1−μ)))²`
with `d = (1 − 2ρ)/√(ρ(1−ρ))`. -/
theorem eq_137 (ρ μ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ρ + Real.sqrt (ρ * (1 - ρ)) *
        (μ * ((1 - 2 * ρ) / Real.sqrt (ρ * (1 - ρ))) + 2 * Real.sqrt (μ * (1 - μ))) =
      (Real.sqrt (μ * (1 - ρ)) + Real.sqrt (ρ * (1 - μ))) ^ 2 := by sorry

end DQI.Semicircle
