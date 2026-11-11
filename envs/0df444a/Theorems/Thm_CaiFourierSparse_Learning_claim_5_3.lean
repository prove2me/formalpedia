-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_claim_5_3
-- name    : CaiFourierSparse.Learning.claim_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:15:39.392543+00:00
-- url     : https://prove2.me/theorems/63c7d3a5-8ee9-4388-9715-4b876aab62c6
-- title:
--   Claim 5.3 — the folded signal $\zeta_w$ has the Haar–Fourier coefficients of $y$, and $\sum_w\|\zeta_w\|^2=\|y\|^2$
-- statement:
--   Let $K=2^a$ and $W$ the Haar types. For every observation $y$ with finite window energy, every type $w\in W$ and every $b\in\mathbb Z$, the folded signal $\zeta_w$ of eq. (52) satisfies
--   $$\widehat{\zeta_w}[b]=\langle y,\varphi_{w_b}\rangle_{[-1,1]},$$
--   and $\sum_{w\in W}\|\zeta_w\|^2_{[-1,1]}=\|y\|^2_{[-1,1]}$.
--
--   Differences from the source:
--   - encoding: the observation y = x + η of Algorithm 1 → any y whose restriction to the window is a.e.-measurable with finite window energy; reason: η is arbitrary, so y ranges over exactly these functions (take x with zero amplitudes)
--   - encoding: K of Algorithm 1 (a power of two) → K = 2^a for every a; reason: Lean representation of the powers of two
--   - encoding: squared L² norms → ℝ≥0∞-valued lower integrals wsq/lsq/osq, real coefficients through ENNReal.ofReal; reason: non-square-integrable functions get energy ∞, so no bound holds through a junk value
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Claim 5.3, printed p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_ApproxAccess

namespace CaiFourierSparse.Learning

open MeasureTheory

/-- Claim 5.3 (printed p. 26, PDF p. 28). For `K = 2^a`, every Haar type `w ∈ W` and every
observation `y` with finite window energy, the folded signal `ζ_w` of (52) has Fourier-series
coefficients `ζ̂_w[b] = ⟨y, φ_{w_b}⟩_{[-1,1]}` for every `b ∈ ℤ`, and
`∑_{w ∈ W} ‖ζ_w‖²_{[-1,1]} = ‖y‖²_{[-1,1]}`. -/
theorem claim_5_3 (a : ℕ) (y : ℝ → ℂ)
    (hy : AEStronglyMeasurable y (volume.restrict window)) (hy2 : wsq y < ⊤) :
    (∀ w ∈ haarTypes a, ∀ b : ℤ, fsc (zeta a w y) b = winner y (phiWB a w b)) ∧
      ∑ w ∈ haarTypes a, wsq (zeta a w y) = wsq y := by sorry

end CaiFourierSparse.Learning
