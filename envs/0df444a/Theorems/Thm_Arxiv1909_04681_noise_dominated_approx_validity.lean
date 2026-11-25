-- Prove2me | Theorems.Thm_Arxiv1909_04681_noise_dominated_approx_validity
-- name    : Arxiv1909_04681.noise_dominated_approx_validity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:49:26.904797+00:00
-- url     : https://prove2.me/theorems/1f0403d0-6f3d-4341-9514-d17a781b81b8
-- title:
--   Eq. (30): range of validity of the noise-dominated approximation
-- statement:
--   Let $P_a(\phi)=\dfrac1{2\pi}+\dfrac{\mathrm{SNR}}{\sqrt{8\pi}}\cos\phi$ be the noise-dominated approximation of eq. (30).
--
--   1. If $0<\mathrm{SNR}<\sqrt{2/\pi}$, then $P_a(\phi)\ge0$ for every $\phi$.
--   2. If $\mathrm{SNR}>\sqrt{2/\pi}$, then $P_a(\phi)<0$ for some $\phi$: the approximation produces negative probabilities.
--
--   **Formalization Note** The paper says the approximation is "valid" for $0<\mathrm{SNR}<\sqrt{2/\pi}$ and that for larger SNR it "breaks down, and can produce negative probabilities". The only precise content of this is non-negativity, which is what is stated.
-- source:
--   Christian and Psaltis, Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise Ratio Regime, arXiv:1909.04681v2 (2020), claim c015; Appendix A, eq. (30) and the sentence after it, PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics

namespace Arxiv1909_04681

theorem noise_dominated_approx_validity :
    (∀ S : ℝ, 0 < S → S < Real.sqrt (2 / Real.pi) → ∀ x : ℝ, 0 ≤ noiseApprox S x) ∧
    (∀ S : ℝ, Real.sqrt (2 / Real.pi) < S → ∃ x : ℝ, noiseApprox S x < 0) := by sorry

end Arxiv1909_04681
