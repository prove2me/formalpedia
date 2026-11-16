-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_Supplement_lemma_4_2
-- name    : ExplicitTensorBarrier694.Explicit.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:40:25.821425+00:00
-- url     : https://prove2.me/theorems/4df29a3f-f462-4aca-bfc0-99284f69aa84
-- title:
--   Lemma 4.2 — Schatten moments of $\sum x_iy_jz_kM_{ijk}$ for random unit vectors
-- statement:
--   Let $n\ge2$ and let $M_{ijk}\in\mathrm{Mat}_r(\mathbb C)$ be arbitrary, $i,j,k\in\{1,\dots,n\}$. Put
--
--   $$H=\sum_{ijk}M_{ijk}M_{ijk}^\dagger,\qquad K=\sum_{ijk}M_{ijk}^\dagger M_{ijk}.$$
--
--   Choose $x,y,z$ independently and uniformly on the unit sphere of $\mathbb C^n$ and set $M=\sum_{ijk}x_iy_jz_kM_{ijk}$. Then
--
--   $$\mathbb E\|M\|_2^2=\frac{\operatorname{tr}H}{n^3},\qquad \mathbb E\|M\|_4^4\le\frac{\|H\|_2^2+\|K\|_2^2}{n^4(n+1)},$$
--
--   where $\|\cdot\|_p$ are Schatten norms ($\|H\|_2$ is the Hilbert–Schmidt norm). No normalization of the $M_{ijk}$ is assumed and no complex conjugation is applied to $x,y,z$.
--
--   Together with Lemma 4.1 this gives the upper bound in Theorem 1.2. This is a paper-proved result awaiting a formal proof.
--
--   Differences from the source:
--   - encoding: x, y, z independent and uniform on the unit sphere of ℂⁿ → the three-fold product of the published OptimalSpectrum.Entangled.uniformSphere n on EuclideanSpace ℂ (Fin n); reason: that measure is Mathlib's sphere measure of Lebesgue measure normalized to mass one, the unitarily invariant probability measure on the sphere of ℂⁿ ≅ ℝ^{2n} for n ≥ 1
--   - encoding: expectation E → Bochner integral against the product measure; reason: the integrands are polynomials in the coordinates, bounded on the sphere, hence integrable for a probability measure; the integral is the expectation
--   - encoding: Schatten norms ‖X‖₂², ‖X‖₄⁴ and tr H → Σ|X_ab|², Re tr((X†X)²) and Re tr H; reason: trace forms of the singular-value definitions; (X†X)² and H are positive semidefinite, so their traces are real
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 4.2, p.12 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Supplement_Flattening
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere

open scoped BigOperators Matrix
open MeasureTheory

namespace ExplicitTensorBarrier694.Explicit.Supplement

open ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 4.2, p.12. For n ≥ 2 and
arbitrary M_{ijk} ∈ Mat_r(ℂ), with H = Σ M M†, K = Σ M† M and x, y, z independent and
uniform on the unit sphere of ℂⁿ (the published unitarily invariant probability measure,
three independent copies), M = Σ x_i y_j z_k M_{ijk} satisfies
E‖M‖₂² = tr H / n³ and E‖M‖₄⁴ ≤ (‖H‖₂² + ‖K‖₂²)/(n⁴(n+1)). -/
theorem lemma_4_2 (n r : ℕ) (hn : 2 ≤ n)
    (M : Fin n → Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ) :
    (∫ w, schatten2Sq (coeffMatrix M (fun i => w.1 i) (fun j => w.2.1 j) (fun k => w.2.2 k))
        ∂((OptimalSpectrum.Entangled.uniformSphere n).prod
          ((OptimalSpectrum.Entangled.uniformSphere n).prod
            (OptimalSpectrum.Entangled.uniformSphere n)))) =
      (Matrix.trace (∑ i, ∑ j, ∑ k, M i j k * (M i j k)ᴴ)).re / (n : ℝ) ^ 3 ∧
    (∫ w, schatten4Pow4 (coeffMatrix M (fun i => w.1 i) (fun j => w.2.1 j) (fun k => w.2.2 k))
        ∂((OptimalSpectrum.Entangled.uniformSphere n).prod
          ((OptimalSpectrum.Entangled.uniformSphere n).prod
            (OptimalSpectrum.Entangled.uniformSphere n)))) ≤
      (schatten2Sq (∑ i, ∑ j, ∑ k, M i j k * (M i j k)ᴴ) +
          schatten2Sq (∑ i, ∑ j, ∑ k, (M i j k)ᴴ * M i j k)) /
        ((n : ℝ) ^ 4 * ((n : ℝ) + 1)) := by sorry

end ExplicitTensorBarrier694.Explicit.Supplement
