-- Prove2me | Theorems.Thm_FalconerPath_starting_pair_coarse_partition
-- name    : FalconerPath.starting_pair_coarse_partition
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:35.245473+00:00
-- url     : https://prove2.me/theorems/b0a9a94d-c62a-4e25-8dd8-0a8ebc7de366
-- title:
--   Pullback of coarse filters preserves mass and product counts
-- statement:
--   Let $d,h,k\in\mathbb N$, let $E\subset\mathbb R^d$ and $r\in\mathbb R$, and let $A$ be a starting geometry for these parameters. Fix $\omega>0$ and a decreasing sequence of Borel relations $\Gamma_N\subset\operatorname{supp}(P_\#\mu_1)\times\operatorname{supp}(P_\#\mu_2)$ whose intersection has positive $(P_\#\mu_1)\otimes(P_\#\mu_2)$ mass. Assume there are one translated dyadic grid and $D\ge0$ such that for every $N$, $\Gamma_N$ is the projected support product intersected with a finite union of depth-$j$ cell pairs for some integer $j\le\omega N+D$.
--
--   Then $\Delta_N=(E_1\times E_2)\cap(P\times P)^{-1}(\Gamma_N)$ is a decreasing family of Borel subsets of $E_1\times E_2$ whose intersection has positive $(\mu_1\otimes\mu_2)$ mass. There is $C_0>0$, independent of $N$, such that every $\Delta_N$ is a disjoint union of at most $C_0 2^{2d\omega N}$ products of spatial Borel sets.
--
--   A starting geometry consists of compact $E_1,E_2\subset E$ equal to the supports of probabilities $\mu_1,\mu_2$ carried by them, common constants $\chi,C>0$ giving all-scale ball bounds $Cr^{d/2+\chi}$, positive cross separation, and one unit $w$ for which all original cross directions lie in $B(w,r)$. It includes continuous linear orthogonal surjections $P:\mathbb R^d\to\mathbb R^{k+1}$ and $Q:\mathbb R^{k+1}\to\mathbb R^{h+1}$, with $h+1\le k+1\le d$. The original, middle, and smallest support pairs are bounded and separated. The two middle laws $P_\#\mu_i$ and the two smallest laws $Q_\#P_\#\mu_i$ share the same all-scale exponent $d/2+\chi$ and constant $C$. The smallest supports are compact. If $d=2k-1$, $P_\#\mu_1+P_\#\mu_2$ vanishes on every affine $k$-plane. The Lean statement isolates the spatial and mass conclusions of the proof and requires availability separately.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, final proof paragraph at “The auxiliary finest-depth cell partition has at most”, “As k+1 ≤ d”, and “pullback preserves disjointness”.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem starting_pair_coarse_partition {d h k : ℕ} {E : Set (Space d)} {r : ℝ}
    (A : StartingGeometry d E r h k) (ω : ℝ) (hω : 0 < ω)
    (Γ : ℕ → PairSet (k+1))
    (hΓ : ∀ N, MeasurableSet (Γ N) ∧
      Γ N ⊆ (Measure.map A.P A.μ₁).support ×ˢ (Measure.map A.P A.μ₂).support)
    (hanti : Antitone Γ)
    (hmass : 0 < ((Measure.map A.P A.μ₁).prod (Measure.map A.P A.μ₂)) (⋂ N, Γ N))
    (hcells : ∃ v : Space (k+1), ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
      ∃ j : ℕ, (j:ℝ) ≤ ω*N+D ∧ CoarseCellPairs
        (Measure.map A.P A.μ₁).support (Measure.map A.P A.μ₂).support (Γ N) v j) :
    let Δ := fun N => supportedPullback A.P A.E₁ A.E₂ (Γ N)
    (∀ N, MeasurableSet (Δ N) ∧ Δ N ⊆ A.E₁ ×ˢ A.E₂) ∧ Antitone Δ ∧
      0 < (A.μ₁.prod A.μ₂) (⋂ N, Δ N) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ N, ProductPartition (Δ N) (C*(scale N)^(2*(d:ℝ)*ω)) := by sorry
end FalconerPath
