-- Prove2me | Theorems.Thm_AgnGaussTomo_lemma_2_8
-- name    : AgnGaussTomo.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:35.494456+00:00
-- url     : https://prove2.me/theorems/bdb1e9a3-ae7f-42a6-b263-af32ba991b1c
-- title:
--   Lemma 2.8 — one Williamson unsqueezing step
-- statement:
--   Let $V$ be the covariance matrix of an $n$-mode Gaussian state (normalized so that the vacuum has $V=I$), and let $\hat V$ be a real symmetric $2n\times2n$ matrix with
--
--   $$
--   0\preceq\hat V-V\preceq\frac{2\zeta}{1-\zeta}\,(V+I)\qquad\text{for some }\zeta\in(0,1).
--   $$
--
--   Let $\hat V=S\hat DS^\top$ be any Williamson decomposition ($S$ symplectic, $\hat D=\operatorname{diag}(d_1,\dots,d_n,d_1,\dots,d_n)$, $d_j>0$). Then the covariance $V'=S^{-1}VS^{-\top}$ obtained by applying the Gaussian unitary of $S^{-1}$ satisfies
--
--   $$
--   \|(V')^{-1}\|_{\mathrm{op}}\le\sqrt{1+\frac{2\zeta}{1-\zeta}\big(\|V^{-1}\|_{\mathrm{op}}+1\big)} .
--   $$
--
--   This is the engine of iterative unsqueezing: an estimate of the covariance with constant relative error turns a squeezing level $\|V^{-1}\|_{\mathrm{op}}$ into roughly its square root, so $\log\log\|V^{-1}\|_{\mathrm{op}}$ rounds bring it down to a constant.
--
--   Differences from the source:
--   - reading: the Gaussian unitary associated with S^{-1} transforms V into V′ = S^{-1}VS^{-⊤} satisfying the bound → the bound for V′ = S^{-1}VS^{-⊤}; reason: that Gaussian unitaries act on covariances by V ↦ SVSᵀ is the §2.2 fact (p. 10); the lemma's content is the bound
--   - encoding: the square root of 1 + 2ζ/(1−ζ)(‖V^{-1}‖_op + 1) → Real.sqrt (1 + 2ζ/(1−ζ) · (‖V^{-1}‖_op + 1)); reason: as printed: the root covers the whole sum, and 2ζ/(1−ζ) multiplies (‖V^{-1}‖_op + 1)
--   - encoding: covariances and means in the order (q₁, …, qₙ, p₁, …, pₙ) → the interleaved order (q₁, p₁, …, qₙ, pₙ) of the published GaussianAt, with symplectic and Williamson data in the grouped order; reason: a relabelling of the same quadratures; norms, traces and the Loewner order are unchanged
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 2.8 (= [BMEM25, Lemma 12]), printed p. 13 (PDF p. 16)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_AgnGaussTomo_grouped
import Definitions.Def_AgnGaussTomo_IsWilliamson
import Definitions.Def_AgnGaussTomo_opNorm

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt InterleavedQuadrature OscillatorCovariance)

namespace AgnGaussTomo

/-- **Lemma 2.8 ([BMEM25, Lemma 12]): one Williamson unsqueezing step.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 2.8,
printed p. 13 (PDF p. 16): "Let V be the covariance matrix of an n-mode Gaussian state, and let V̂ be
a real symmetric matrix satisfying 0 ⪯ V̂ − V ⪯ 2ζ/(1 − ζ) (V + I) (13) for some ζ ∈ (0, 1). Take a
Williamson decomposition V̂ = S D̂ Sᵀ, where S is symplectic and D̂ = diag(d₁, …, dₙ, d₁, …, dₙ) with
d_j > 0. Then the Gaussian unitary associated with S^{-1} transforms V into V′ = S^{-1} V S^{-⊤}
satisfying ‖(V′)^{-1}‖_op ≤ sqrt(1 + 2ζ/(1 − ζ) (‖V^{-1}‖_op + 1))."

**Formalization Note.** `V`, `V̂` are indexed by the interleaved quadratures of the published
`GaussianAt` (vacuum covariance `I`, the paper's normalization); the Williamson decomposition and
`V′` are in the grouped ordering (`grouped`), which does not change `‖·‖_op`. The square root covers
`1 + (2ζ/(1−ζ))(‖V^{-1}‖_op + 1)`, as printed. `⪯` is the Loewner order (`PosSemidef` of the
difference). Matrix inverses are `Matrix.inv` (both `V` and `V′` are positive definite). -/
theorem lemma_2_8 (n : ℕ) (V Vhat : OscillatorCovariance (Fin n))
    (hV : ∃ (τ : State (Occupation (Fin n))) (d : InterleavedQuadrature (Fin n) → ℝ),
      GaussianAt τ.coefficients d V)
    (hsymm : Vhat.transpose = Vhat) (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hlow : (Vhat - V).PosSemidef)
    (hup : ((2 * ζ / (1 - ζ)) • (V + 1) - (Vhat - V)).PosSemidef)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n → ℝ)
    (hW : IsWilliamson (grouped Vhat) S d) :
    opNorm ((S⁻¹ * grouped V * (S⁻¹).transpose)⁻¹) ≤
      Real.sqrt (1 + 2 * ζ / (1 - ζ) * (opNorm V⁻¹ + 1)) := by sorry

end AgnGaussTomo
