-- Prove2me | Theorems.Thm_FalconerPath_starting_pair_projected_patches
-- name    : FalconerPath.starting_pair_projected_patches
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:33.264994+00:00
-- url     : https://prove2.me/theorems/0bbd2d6e-1fb3-4205-8b8f-825b6f21eace
-- title:
--   Compatible projections and separated compact starting patches
-- statement:
--   Let $d\ge2$, let $E\subset\mathbb R^d$ be compact with $\dim_H E>d/2$, and let $\rho$ be a probability carried by $E$. Suppose $s>d/2$, $K>0$, and $\rho(B(z,u))\le Ku^s$ for all centers and $0<u\le1$. Assume that for every integer $k\ge2$ with $d=2k-1$, $\rho$ gives zero mass to every affine $k$-plane. Fix $r>0$.
--
--   There are integers $h,k$ with $h\ge1$ such that either $d=2h$ and $k=h$, or $k\ge2$, $d=2k-1$, and $h+1=k$, and there exists a starting geometry for $d,E,r,h,k$.
--
--   A starting geometry consists of compact $E_1,E_2\subset E$ equal to the supports of probabilities $\mu_1,\mu_2$ carried by them, common constants $\chi,C>0$ giving all-scale ball bounds $Cr^{d/2+\chi}$, positive cross separation, and one unit $w$ for which all original cross directions lie in $B(w,r)$. It includes continuous linear orthogonal surjections $P:\mathbb R^d\to\mathbb R^{k+1}$ and $Q:\mathbb R^{k+1}\to\mathbb R^{h+1}$, with $h+1\le k+1\le d$. The original, middle, and smallest support pairs are bounded and separated. The two middle laws $P_\#\mu_i$ and the two smallest laws $Q_\#P_\#\mu_i$ share the same all-scale exponent $d/2+\chi$ and constant $C$. The smallest supports are compact. If $d=2k-1$, $P_\#\mu_1+P_\#\mu_2$ vanishes on every affine $k$-plane. The Lean statement bundles the projected patch construction into an intermediate record without a radial-density or filter conclusion.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, second proof paragraph from “In both parities project further” through “Normalize and decrease the common exponent”. Its odd-dimensional zero-hyperplane preparation also uses the end of the first proof paragraph.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem starting_pair_projected_patches {d : ℕ} (hd : 2 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E) (hdim : (d:ℝ≥0∞)/2 < dimH E)
    (ρ : Measure (Space d)) (hρ : Probability ρ) (hcarried : Carried ρ E)
    (s K : ℝ) (hs : (d:ℝ)/2 < s) (hK : 0 < K) (hf : Frostman ρ s K)
    (hzero : ∀ k : ℕ, 2 ≤ k → d = 2*k-1 → NoAffineMass ρ k)
    (r : ℝ) (hr : 0 < r) :
    ∃ h k : ℕ, 1 ≤ h ∧
      ((d = 2*h ∧ k = h) ∨ (2 ≤ k ∧ d = 2*k-1 ∧ h+1 = k)) ∧
      Nonempty (StartingGeometry d E r h k) := by sorry
end FalconerPath
