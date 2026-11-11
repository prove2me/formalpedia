-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_6
-- name    : DetSpectralSparsify.Dense.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:34.365661+00:00
-- url     : https://prove2.me/theorems/1ca553c2-9a4a-40cd-b3f8-1c4a66e6919c
-- title:
--   Lemma 6 (Inexact candidate scores) — scores within ζ = R/(16εk) still give the (1±ε) guarantee
-- statement:
--   In the setting of Lemma 5 ($q\ge1$, $0\preceq A_i\preceq RI$, $\frac1q\sum_iA_i=I$, $R\ge1$, $0<\varepsilon\le1/2$, $k\ge4R\varepsilon^{-2}\ln(4r)$), suppose that at every iteration the candidate scores
--   $$u_j\langle e^{\theta_+S},A_i\rangle-\ell_j\langle e^{-\theta_-S},A_i\rangle$$
--   are computed for all candidates with additive error at most
--   $$\zeta:=\frac{R}{16\varepsilon k}.$$
--   Choosing a candidate of minimum approximate value still yields
--   $$(1-\varepsilon)I\;\preceq\;\frac1k\sum_{j=1}^kA_{i_j}\;\preceq\;(1+\varepsilon)I .$$
--
--   This is the tolerance met by the dense and sparse score implementations.
--
--   **Formalization Note** The approximate scores are arbitrary real numbers within $\zeta$ of the exact scores (definition `IsApproxAlg1Selection`); they may depend on the earlier choices of the run.
--
--   Differences from the source:
--   - encoding: matrices A_1, …, A_q → hypothesis 0 < q; reason: the list notation presumes a nonempty family
--   - reading: scores computed with additive error at most ζ and a candidate of minimum approximate value chosen → there exist approximate scores σ̃_j(i) with |σ̃_j(i) − σ_j(i)| ≤ ζ for all i, j, and each i_j minimizes σ̃_j; reason: covers every way of computing the approximations, including adaptive ones
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.8, Lemma 6

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph
import Definitions.Def_DetSpectralSparsify_Dense_MatrixChernoff

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 6 (Inexact candidate scores), p.8. In the setting of Lemma 5, if at every iteration
the scores `u_j ⟨e^{θ₊S}, A_i⟩ - ℓ_j ⟨e^{-θ₋S}, A_i⟩` of all candidates are computed with additive
error at most `ζ = R/(16 ε k)` and a candidate of minimum approximate value is chosen, then
`(1-ε) I ⪯ (1/k) ∑_j A_{i_j} ⪯ (1+ε) I`. -/
theorem lemma_6 {r q k : ℕ} (A : Fin q → Matrix (Fin r) (Fin r) ℝ) (R ε : ℝ)
    (hq : 0 < q) (hA : ∀ i, (A i).PosSemidef) (hAR : ∀ i, PSDLe (A i) (R • 1))
    (havg : (q : ℝ)⁻¹ • ∑ i, A i = 1) (hR : 1 ≤ R) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hk : 4 * R * (ε ^ 2)⁻¹ * Real.log (4 * r) ≤ k) :
    ∀ idx : Fin k → Fin q, IsApproxAlg1Selection A R ε idx →
      PSDLe ((1 - ε) • (1 : Matrix (Fin r) (Fin r) ℝ)) ((k : ℝ)⁻¹ • ∑ j, A (idx j)) ∧
      PSDLe ((k : ℝ)⁻¹ • ∑ j, A (idx j)) ((1 + ε) • (1 : Matrix (Fin r) (Fin r) ℝ)) := by sorry

end DetSpectralSparsify.Dense
