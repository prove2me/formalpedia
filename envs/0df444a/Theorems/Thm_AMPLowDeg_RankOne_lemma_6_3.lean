-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_6_3
-- name    : AMPLowDeg.RankOne.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:05:30.396365+00:00
-- url     : https://prove2.me/theorems/3ef53a43-6b05-4239-b281-a5d794e0d877
-- title:
--   Lemma 6.3 — core-cumulant $L^2$ bound (6.7)
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$, and let $H$ be the field (4.2) with $s=q_{\mathrm{AMP}}$. Fix a rooted core $\gamma$ with $e=|\gamma|\le D$, $v=|V(\gamma)|$ and $g=\tau(\gamma)$. Then
--
--   $$
--   \mathbb E\big[C_\gamma(H)^2\big]\le(D+1)^{2g}(2D+1)^{36g}\,2^{8g}\,M_D^{16g},\qquad M_D=\max\{1,\|\Theta\|_{4D+2}\}.
--   $$
--
--   The high-moment cost grows with the core excess $g$ only, not with the length of its degree-two chains; summed over cores this gives Lemma 2.5(2).
--
--   Differences from the source:
--
--   - encoding: exponents 2g, 36g, 8g, 16g with g = τ(γ) → integer powers (zpow) with the integer excess τ(γ); reason: τ(γ) ≥ 1 for a rooted core, so these are the ordinary powers
--   - encoding: A_α(θ) and C_γ(H) on the probability space of (θ, W, Z) → on the space of (θ, Z) with law π^{⊗n} ⊗ 𝒩(0, I_n) (chanLaw); R = √s θ + Z, H = sθ + √s Z; reason: W is independent of (θ, Z) and enters neither A_α nor C_γ(H), so the expectations are the same
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 19, Lemma 6.3, eq. (6.7); proof pp. 19–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential
import Definitions.Def_AMPLowDeg_RankOne_Graph
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma 6.3, p. 19 — core-cumulant `L²` bound (6.7): for a rooted core `γ` with `e = |γ| ≤ D`
and `g = τ(γ)`, and `H` the field (4.2) at `s = q_AMP`,
`E[C_γ(H)²] ≤ (D + 1)^{2g} (2D + 1)^{36g} 2^{8g} M_D^{16g}`, `M_D = max{1, ‖Θ‖_{4D+2}}`.
Vertex `1` is `⟨0, hn⟩`. -/
theorem lemma_6_3 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n D : ℕ) (hn : 0 < n) (γ : Edge n → ℕ)
    (hγ : IsRootedCore ⟨0, hn⟩ γ) (hD : absIdx γ ≤ D) :
    ∫ w, (Ccum π (qAMP π) ⟨0, hn⟩ γ (Hfield (qAMP π) w)) ^ 2 ∂(chanLaw π n) ≤
      ((D : ℝ) + 1) ^ (2 * excess γ) * (2 * (D : ℝ) + 1) ^ (36 * excess γ) *
        (2 : ℝ) ^ (8 * excess γ) * MD π D ^ (16 * excess γ) := by sorry

end AMPLowDeg.RankOne
