-- Prove2me | Theorems.Thm_FalconerPath_starting_pair_radial_pullback
-- name    : FalconerPath.starting_pair_radial_pullback
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:31.388927+00:00
-- url     : https://prove2.me/theorems/9513c3c3-f7a6-4061-95df-38c75b274177
-- title:
--   Pull compact radial restrictions back to original patches
-- statement:
--   Let $d,h,k\in\mathbb N$, let $E\subset\mathbb R^d$, let $r\in\mathbb R$, and let $A$ be a starting geometry for these parameters. Put $\eta_i=Q_\#P_\#\mu_i$. Let $p>1$ and let $K_i\subset\operatorname{supp}\eta_i$ be compact with $\eta_i(K_i)>0$. Suppose $L>0$ and the normalized restrictions $\eta_i^\prime=\eta_i|_{K_i}/\eta_i(K_i)$ have, in both orientations, jointly measurable nonnegative radial surface densities whose $p$th power integrals are at most $L$ at every pin in the corresponding support.
--
--   There is a new starting geometry $B$ for the same $d,E,r,h,k$ with $B.E_i\subset A.E_i$, the same maps $P,Q$, and the same gap $\chi$. For some $L^\prime>0$, its smallest projected laws have jointly measurable nonnegative radial densities in both orientations whose $p$th power integrals are bounded by $L^\prime$ at every support pin.
--
--   A starting geometry consists of compact $E_1,E_2\subset E$ equal to the supports of probabilities $\mu_1,\mu_2$ carried by them, common constants $\chi,C>0$ giving all-scale ball bounds $Cr^{d/2+\chi}$, positive cross separation, and one unit $w$ for which all original cross directions lie in $B(w,r)$. It includes continuous linear orthogonal surjections $P:\mathbb R^d\to\mathbb R^{k+1}$ and $Q:\mathbb R^{k+1}\to\mathbb R^{h+1}$, with $h+1\le k+1\le d$. The original, middle, and smallest support pairs are bounded and separated. The two middle laws $P_\#\mu_i$ and the two smallest laws $Q_\#P_\#\mu_i$ share the same all-scale exponent $d/2+\chi$ and constant $C$. The smallest supports are compact. If $d=2k-1$, $P_\#\mu_1+P_\#\mu_2$ vanishes on every affine $k$-plane. The Lean statement isolates the compact pullback step, allows the common Frostman constant to change, and preserves the gap and projection maps explicitly.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, third proof paragraph at “pull its positive compact restrictions back to the original measures”, “Inner regularity permits positive compact preimages”, and “further restriction preserves all established bounds”.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem starting_pair_radial_pullback {d h k : ℕ} {E : Set (Space d)} {r : ℝ}
    (A : StartingGeometry d E r h k) (p : ℝ) (hp : 1 < p)
    (K₁ K₂ : Set (Space (h+1))) (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂)
    (hs₁ : K₁ ⊆ (Measure.map A.Q (Measure.map A.P A.μ₁)).support)
    (hs₂ : K₂ ⊆ (Measure.map A.Q (Measure.map A.P A.μ₂)).support)
    (hm₁ : 0 < (Measure.map A.Q (Measure.map A.P A.μ₁)) K₁)
    (hm₂ : 0 < (Measure.map A.Q (Measure.map A.P A.μ₂)) K₂)
    (L : ℝ) (hL : 0 < L)
    (hlp : UniformRadialLp
      (normalizedRestriction (Measure.map A.Q (Measure.map A.P A.μ₁)) K₁)
      (normalizedRestriction (Measure.map A.Q (Measure.map A.P A.μ₂)) K₂) p L) :
    ∃ B : StartingGeometry d E r h k,
      B.E₁ ⊆ A.E₁ ∧ B.E₂ ⊆ A.E₂ ∧ B.P = A.P ∧ B.Q = A.Q ∧ B.χ = A.χ ∧
      ∃ L' : ℝ, 0 < L' ∧ UniformRadialLp
        (Measure.map B.Q (Measure.map B.P B.μ₁))
        (Measure.map B.Q (Measure.map B.P B.μ₂)) p L' := by sorry
end FalconerPath
