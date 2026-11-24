-- Prove2me | Theorems.Thm_CompressedSensingRadar_bp_recovers_random_phase_signal
-- name    : CompressedSensingRadar.bp_recovers_random_phase_signal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:07:40.014811+00:00
-- url     : https://prove2.me/theorems/d37434e4-f7ae-4a3d-b562-2e23a60c8250
-- title:
--   Proposition 2 (Tropp, Theorem 14): BP recovers a random signal on a well-conditioned support
-- statement:
--   Let $\Phi\in\mathbb{C}^{N\times N^2}$ have unit-norm atoms and coherence $\mu$. Fix a support $T$ with $K=|T|$ such that $\Phi_T$ has least singular value $\sigma_{\min}(\Phi_T)\ge1/\sqrt2$. Let $\zeta>0$ with
--
--   $$8\mu^2K\le\frac1{\log(N^2/\zeta)}.$$
--
--   Let $s$ be a random signal supported on $T$: its coefficients on $T$ are independent standard complex Gaussians, so their phases are independent and uniform on $[0,2\pi)$. Set $y=\Phi s$. Then $s$ is the unique solution of basis pursuit, except with probability at most $2\zeta$:
--
--   $$\mathbb{P}\{\text{BP recovers }s\text{ from }y\}\ge1-2\zeta.$$
--
--   **Formalization Note** The coefficients follow the paper's random-signal model, which is the case used in the proof of Theorem 2. Tropp's Theorem 14 needs only independent uniform phases and allows arbitrary magnitudes.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Appendix A, Proposition 2, p. 13 (citing Tropp, On the conditioning of random subdictionaries, 2008, Theorem 14)

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem bp_recovers_random_phase_signal (N : ℕ) (Φ : Matrix (Fin N) (Fin (N ^ 2)) ℂ)
    (hΦ : HasUnitAtoms Φ) (T : Finset (Fin (N ^ 2))) (ζ : ℝ) (hζ : 0 < ζ)
    (hK : 8 * coherence Φ ^ 2 * T.card ≤ 1 / Real.log ((N : ℝ) ^ 2 / ζ))
    (hσ : LeastSingValGe (subdict Φ T) (1 / Real.sqrt 2)) :
    1 - 2 * ζ ≤ bpProbOnSupport Φ T := by sorry

end CompressedSensingRadar
