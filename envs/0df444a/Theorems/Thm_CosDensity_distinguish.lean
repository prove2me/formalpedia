-- Prove2me | Theorems.Thm_CosDensity_distinguish
-- name    : CosDensity.distinguish
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:38:26.320239+00:00
-- url     : https://prove2.me/theorems/f2d2c9ed-d1cb-494c-a123-b97b5be023f3
-- title:
--   §8.7 — a $(1+\epsilon_p)$-approximation distinguishes $z_q=0$ from $z_q=1$
-- statement:
--   Let $0<X_0$, $\varphi>1$, $\varphi X_0\le X_1$ and $0<\epsilon<(\varphi-1)/(\varphi+1)$. Then $(1+\epsilon)X_0<(1-\epsilon)X_1$. Consequently, if $0\le M_0\le X_0$ and $M_1\ge X_1$, every $(1+\epsilon)$-approximation of $M_0$ is strictly smaller than every $(1+\epsilon)$-approximation of $M_1$.
--
--   With $X_0=V_0(q)+\kappa_p\nu Q^p$ and $X_1=V_0(q)+\kappa_pQ^p$ (bounds (37)–(38)), a $(1+\epsilon_p)$-approximation of $M_p(P(z,q))$ determines $z_q$.
--
--   Differences from the source:
--   - generalization: the two cases z_q = 0, 1 of M_p(P(z, q)) with ratio φ_p → arbitrary values M₀ ≤ X₀ and M₁ ≥ X₁ with φ X₀ ≤ X₁; reason: the paper's moments are an instance
--   - reading: can be used to distinguish the two cases → the approximation intervals are strictly separated: Y₀ < Y₁; reason: separation is what distinguishing means
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.7, p.36 (pdf_page 37)

import Mathlib
import Definitions.Def_CosDensity_Stream

namespace CosDensity

/-- **Distinguishing the two cases** (§8.7). Q. Zhang, *Frequency Moments Beyond Equality:
Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.7, p.36
(pdf_page 37): "Consequently, for any ϵ_p ∈ (0, (φ_p − 1)/(φ_p + 1)), a (1 + ϵ_p)-approximation to
M_p(P(z, q)) can be used to distinguish the two cases z_q = 0 and z_q = 1."

Let `0 < X₀`, `φ > 1`, `φ X₀ ≤ X₁` and `0 < ε < (φ − 1)/(φ + 1)`. Then `(1 + ε) X₀ < (1 − ε) X₁`,
and every `(1+ε)`-approximation of a value `M₀ ∈ [0, X₀]` is strictly smaller than every
`(1+ε)`-approximation of a value `M₁ ≥ X₁`.

**Formalization Note.** The paper's instance is `X₀ = V₀(q) + κ_p ν Q^p` (the bound (37) for
`z_q = 0`) and `X₁ = V₀(q) + κ_p Q^p` (the bound (38) for `z_q = 1`), with `φ = φ_p`. -/
theorem distinguish (X₀ X₁ φ ε : ℝ) (hX₀ : 0 < X₀) (hφ : 1 < φ) (hX : φ * X₀ ≤ X₁)
    (hε0 : 0 < ε) (hε : ε < (φ - 1) / (φ + 1)) :
    (1 + ε) * X₀ < (1 - ε) * X₁ ∧
      ∀ M₀ M₁ Y₀ Y₁ : ℝ, 0 ≤ M₀ → M₀ ≤ X₀ → X₁ ≤ M₁ →
        IsApprox ε M₀ Y₀ → IsApprox ε M₁ Y₁ → Y₀ < Y₁ := by sorry

end CosDensity
