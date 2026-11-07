-- Prove2me | Theorems.Thm_CosDensity_phi_ratio
-- name    : CosDensity.phi_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:46.773374+00:00
-- url     : https://prove2.me/theorems/9d9028bb-9f58-4624-819c-d295b9d74b4c
-- title:
--   §8.7 — the ratio $\varphi_p=(C_V+\kappa_p)/(C_V+\kappa_p\nu)>1$
-- statement:
--   Let $Q>0$, $0<\nu<1$, $\kappa>0$ and $0\le V\le C_VQ^p$. Then
--
--   $$\varphi:=\frac{C_V+\kappa}{C_V+\kappa\nu}>1\qquad\text{and}\qquad\frac{V+\kappa Q^p}{V+\kappa\nu Q^p}\ge\varphi .$$
--
--   In the paper $V=V_0(q)$, $\kappa=\kappa_p$, $\nu=1/10$ and $C_V$ is the constant of Lemma 8.8, so $\varphi=\varphi_p$ is a constant ratio between the one-case and the zero-case bounds.
--
--   Differences from the source:
--   - generalization: V = V₀(q) with V₀(q)/Q^p ∈ [0, C_V], κ = κ_p, ν = 1/10, Q the query amplitude → arbitrary reals V, C_V, Q > 0, 0 < ν < 1, κ > 0 with 0 ≤ V ≤ C_V Q^p; reason: the step is arithmetic; the paper's values are an instance
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.7, p.35 (pdf_page 36)

import Mathlib

namespace CosDensity

/-- **The ratio `φ_p`** (§8.7). Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine
Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.7, p.35 (pdf_page 36):
"By Lemma 8.8, we know V₀(q)/Q^p ∈ [0, C_V]. We choose φ_p := (C_V + κ_p)/(C_V + κ_p ν) > 1.
Thus, (V₀(q) + κ_p Q^p)/(V₀(q) + κ_p ν Q^p) ≥ φ_p."

For reals with `Q > 0`, `0 < ν < 1`, `κ > 0` and `0 ≤ V ≤ C_V Q^p`, the ratio
`φ = (C_V + κ)/(C_V + κ ν)` exceeds `1` and is at most `(V + κ Q^p)/(V + κ ν Q^p)`.

**Formalization Note.** The paper's instance is `V = V₀(q)`, `Q` the query amplitude, `κ = κ_p`,
`ν = 1/10` and `C_V` the constant of Lemma 8.8; the statement is the arithmetic step for every such
choice. -/
theorem phi_ratio (p : ℕ) (V CV Q ν κ : ℝ) (hQ : 0 < Q) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hκ : 0 < κ) (hV0 : 0 ≤ V) (hV : V ≤ CV * Q ^ p) :
    1 < (CV + κ) / (CV + κ * ν) ∧
      (CV + κ) / (CV + κ * ν) ≤ (V + κ * Q ^ p) / (V + κ * ν * Q ^ p) := by sorry

end CosDensity
