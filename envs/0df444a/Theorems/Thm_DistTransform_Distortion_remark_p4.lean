-- Prove2me | Theorems.Thm_DistTransform_Distortion_remark_p4
-- name    : DistTransform.Distortion.remark_p4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:35.934155+00:00
-- url     : https://prove2.me/theorems/76d27089-7b50-4485-8d57-f328a9dfd195
-- title:
--   Remark, p. 4 — the law of F^{-1}(h(U)) is T_g(F) with g(x) = P(h(U) ⩽ x)
-- statement:
--   Let $h:(0,1)\to(0,1]$ be increasing on $(0,1)$, let $U$ be uniformly distributed on $(0,1)$, and set
--   $$
--   g(x)=\mathbb P\big(h(U)\le x\big),\qquad x\in\mathbb R.
--   $$
--   Then
--
--   1. $g\in\mathcal H_0$;
--   2. for every distribution $F$ with bounded support, the law of $F^{-1}(h(U))$ has cdf $g\circ F$, that is $\mathbb P\big(F^{-1}(h(U))\le x\big)=g(F(x))$ for every $x\in\mathbb R$;
--   3. if moreover $h(p)<1$ for every $p\in(0,1)$, the same identity holds for every distribution $F$ on $\mathbb R$.
--
--   Thus the transform $F\mapsto\mathrm{law}(F^{-1}(h(U)))$ is the probability distortion $T_g$, on $\mathcal M_\infty$ in general and on $\mathcal M_0$ when $h$ avoids $1$. Combined with eq. (4) and its extension to $\mathcal M_0$, this concludes the "only if" direction of Theorem 1.
--
--   **Formalization Note** $\mathbb P$ is Lebesgue measure restricted to $(0,1)$, and the law of $F^{-1}(h(U))$ is described through its cdf, $x\mapsto\mathbb P(F^{-1}(h(U))\le x)$, so no pushforward along a possibly non-measurable map is involved. The paper's "defines to a probability transform" is read as "defines a probability distortion".
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 4, remark after Definition 1 (alternative formulation)

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Remark on p. 4 (alternative formulation): for an increasing `h : (0, 1) → (0, 1]` and `U`
uniform on `(0, 1)`, put `g(x) = P(h(U) ≤ x)`. Then `g ∈ H0`, and for every `F ∈ M∞` the law
of `F⁻¹(h(U))` has cdf `g ∘ F`; if moreover `h < 1`, the same holds for every `F ∈ M0`. -/
theorem remark_p4 (h : ℝ → ℝ) (hh_mono : MonotoneOn h (Set.Ioo 0 1))
    (hh_range : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1) :
    IsH0 (fun x => (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ x}) ∧
      (∀ F ∈ Minf, ∀ x : ℝ,
        (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile F (h p) ≤ x} =
          (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ cdf (F : Measure ℝ) x}) ∧
      ((∀ p ∈ Set.Ioo (0 : ℝ) 1, h p < 1) → ∀ (F : ProbabilityMeasure ℝ) (x : ℝ),
        (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile F (h p) ≤ x} =
          (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ cdf (F : Measure ℝ) x}) := by sorry

end DistTransform.Distortion
