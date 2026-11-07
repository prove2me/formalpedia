-- Prove2me | Theorems.Thm_ContinualCounting_sigma_attained
-- name    : ContinualCounting.sigma_attained
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:19.747676+00:00
-- url     : https://prove2.me/theorems/92617f56-3957-4100-9672-5561c03c0630
-- title:
--   §5, p.19 — a measurable minimizer exists
-- statement:
--   Let $\nu$ be a probability law of $z$ on $\mathbb R^{2^h}$ and $u$ a node. There is a measurable $\varphi$ of the coefficients $\Delta^{<\ell(\ell(u))}(z),\Delta^{<\ell(r(u))}(z)$ with
--   $$\mathbb E\big[|b_{r(u)}-\varphi(\Delta^{<\ell(\ell(u))}(z),\Delta^{<\ell(r(u))}(z))|\big]=\sigma_{u,\ell},$$
--   and a measurable $\varphi$ of $\Delta^{<r(\ell(u))}(z),\Delta^{<r(r(u))}(z)$ with
--   $$\mathbb E\big[|b_{r(\ell(u))}-b_{r(u)}-b_{r(r(u))}-\varphi(\Delta^{<r(\ell(u))}(z),\Delta^{<r(r(u))}(z))|\big]=\sigma_{u,r}.$$
--
--   These are the paper's $m^u_\ell$ and $m^u_r$, the predictors used by the mechanism $\widehat M_s$, and they connect Lemma 5's prediction error to $\sigma$.
--
--   Differences from the source:
--   - reading: "a measurable minimizer m of inf_m E[|·| | ·], chosen as the smallest conditional median" → there is a measurable φ attaining the infimum defining σ; reason: the paper defines m^u by this property; the smallest conditional median is one witness, and the proof uses only attainment
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_ContinualCounting_sigmaL

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **A measurable minimizer exists.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), p.19:
"we also define m^u_ℓ(∆^{<ℓ(ℓ(u))}(z), ∆^{<ℓ(r(u))}(z)) as a measurable minimizer m of
inf_m E[|b_{r(u)} − m| | ∆^{<ℓ(ℓ(u))}(z), ∆^{<ℓ(r(u))}(z)]", and likewise `m^u_r`.

**Formalization Note.** Stated as the attainment of the infima `sigmaL`, `sigmaR` by a measurable function of
the conditioning coefficients, which is what the use of `m^u_ℓ, m^u_r` in the proof of Lemma 5 requires.
The paper's choice, the smallest conditional median, is one such minimizer. -/
theorem sigma_attained {h : ℕ} (ν : Measure (Fin (2 ^ h) → ℝ)) [IsProbabilityMeasure ν] (u : Node) :
    (∃ φ : (condSetL h u → ℝ) → ℝ, Measurable φ ∧
      ∫⁻ z, ‖targetL h u z - φ (fun v => coef h v.1 z)‖ₑ ∂ν = sigmaL ν u) ∧
    (∃ φ : (condSetR h u → ℝ) → ℝ, Measurable φ ∧
      ∫⁻ z, ‖targetR h u z - φ (fun v => coef h v.1 z)‖ₑ ∂ν = sigmaR ν u) := by sorry

end ContinualCounting
