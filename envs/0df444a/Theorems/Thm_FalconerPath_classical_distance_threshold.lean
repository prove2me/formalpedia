-- Prove2me | Theorems.Thm_FalconerPath_classical_distance_threshold
-- name    : FalconerPath.classical_distance_threshold
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:31.275588+00:00
-- url     : https://prove2.me/theorems/28b225f6-d73e-4d72-905b-8d829e15b8b6
-- title:
--   The classical distance threshold
-- statement:
--   Let $n\ge2$ be an integer and let $\rho$ be a Borel probability on $\mathbb R^n$ with compact support. Suppose $C>0$ and $s>(n+1)/2$, and suppose $\rho(B(z,r))\le Cr^s$ for every center $z$ and every $0<r\le1$. Then $\Delta(\operatorname{supp}\rho)=\{|x-y|:x,y\in\operatorname{supp}\rho\}$ has positive Lebesgue measure.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.2, Lemma 5.5 (The classical distance threshold), label prep:classical-plane. Its proof identifies the classical threshold argument as Falconer1985.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem classical_distance_threshold {n : ℕ} (hn : 2 ≤ n)
    (ρ : Measure (Space n)) (hp : Probability ρ) (hc : IsCompact ρ.support)
    (s C : ℝ) (hs : ((n:ℝ)+1)/2 < s) (hC : 0 < C)
    (hf : Frostman ρ s C) :
    0 < volume (distanceSet ρ.support) := by sorry
end FalconerPath
