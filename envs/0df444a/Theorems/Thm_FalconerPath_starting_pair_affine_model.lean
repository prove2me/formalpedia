-- Prove2me | Theorems.Thm_FalconerPath_starting_pair_affine_model
-- name    : FalconerPath.starting_pair_affine_model
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:41.774321+00:00
-- url     : https://prove2.me/theorems/987ea74b-36d7-492e-b4b2-16ab5825dc10
-- title:
--   A charged affine plane supplies an original-distance model
-- statement:
--   Let $d,n\in\mathbb N$, let $E\subset\mathbb R^d$ be compact, and let $\rho$ be a probability carried by $E$. Let $s\in\mathbb R$ and $K>0$, and assume $\rho(B(z,r))\le Kr^s$ for every center and $0<r\le1$. If $V\subset\mathbb R^d$ is an affine subspace of dimension $n$ with $\rho(V)>0$, then there is a probability $\eta$ on $\mathbb R^n$ with compact support and some $K^\prime>0$ such that $\eta(B(z,r))\le K^\prime r^s$ for every center and $0<r\le1$, and
--
--   $$\Delta(\operatorname{supp}\eta)\subset\Delta(E).$$
--
--   The Lean statement isolates the isometric model and distance inclusion from the proof and does not yet assert the classical positive-distance conclusion.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, first proof paragraph at “its normalized positive restriction to that plane still has this exponent”, “applied isometrically within the plane”, and “These are original distances”.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem starting_pair_affine_model {d n : ℕ} (E : Set (Space d))
    (hE : IsCompact E) (ρ : Measure (Space d)) (hρ : Probability ρ)
    (hcarried : Carried ρ E) (s K : ℝ) (hK : 0 < K) (hf : Frostman ρ s K)
    (V : AffineSubspace ℝ (Space d)) (hV : Module.finrank ℝ V.direction = n)
    (hpos : 0 < ρ (V : Set _)) :
    ∃ η : Measure (Space n), Probability η ∧ IsCompact η.support ∧
      ∃ K' : ℝ, 0 < K' ∧ Frostman η s K' ∧ distanceSet η.support ⊆ distanceSet E := by sorry
end FalconerPath
