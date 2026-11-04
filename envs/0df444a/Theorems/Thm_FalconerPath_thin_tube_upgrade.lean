-- Prove2me | Theorems.Thm_FalconerPath_thin_tube_upgrade
-- name    : FalconerPath.thin_tube_upgrade
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:32.067313+00:00
-- url     : https://prove2.me/theorems/da83fba3-4e30-48c3-b42d-78315ad21cbb
-- title:
--   From integer to half-integer directional availability
-- statement:
--   Let $k\ge2$, $k-\tfrac12<s<k$, and $K>0$. Let $\nu,\rho$ be fixed probabilities on $\mathbb R^{k+1}$ with bounded positively separated supports and all-scale ball bounds $Kr^s$ for every center and $0<r\le1$. Let $G_N$ be Borel pair relations. Suppose there are fixed $\zeta,C>0$ such that both unnormalized directional laws of every $G_N$ have directional plate bounds $Cu^\zeta$ for $2^{-N}\le u\le1$, at almost every corresponding pin.
--
--   Assume $k-1$ is available for this family. Then $k-\tfrac12$ is available. More explicitly, availability of $q$ means that for every $e>0$ there exist $c,C_e>0$ and $N_0$ such that for each $N\ge N_0$ a Borel $B_N\subset G_N$ has $(\nu\otimes\rho)(B_N)\le C_e2^{-cN}$, and both directional laws on $G_N\setminus B_N$ give every radius-$u$ cap mass at most $2^{eN}u^q$ for $2^{-N}\le u\le1$, at almost every corresponding pin. The conclusion is this property with $q=k-\tfrac12$, given it with $q=k-1$. Lean makes Borelness, the fixed laws, and uniform plate constants explicit.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.1, Proposition 5.4 (Thin-tube upgrade), label prep:thin-upgrade, using Definition 5.1 (Availability), label prep:availability.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem thin_tube_upgrade {k : ℕ} (hk : 2 ≤ k) (s K : ℝ)
    (hs : (k:ℝ)-1/2 < s) (hsk : s < k) (hK : 0 < K)
    (ν ρ : Measure (Space (k+1))) (hν : Probability ν) (hρ : Probability ρ)
    (hsep : HasBoundedSeparated ν ρ)
    (hfν : Frostman ν s K) (hfρ : Frostman ρ s K)
    (G : ℕ → PairSet (k+1)) (hG : ∀ N, MeasurableSet (G N))
    (ζ C : ℝ) (hζ : 0 < ζ) (hC : 0 < C)
    (hplates : ∀ N, bothPlates ν ρ (G N) ζ C (mesh N))
    (havailable : Available ν ρ G ((k:ℝ)-1)) :
    Available ν ρ G ((k:ℝ)-1/2) := by sorry
end FalconerPath
