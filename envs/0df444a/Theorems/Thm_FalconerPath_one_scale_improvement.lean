-- Prove2me | Theorems.Thm_FalconerPath_one_scale_improvement
-- name    : FalconerPath.one_scale_improvement
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:33.774873+00:00
-- url     : https://prove2.me/theorems/64521fa6-b254-48f0-a6e2-7901ae595bef
-- title:
--   Uniform one-scale improvement of directional cap exponents
-- statement:
--   Fix an integer $k\ge2$, $k-\tfrac12<s<k$, $k-1\le q<k-\tfrac12$, and positive constants $\zeta,L,a,K,C$. There are $\varepsilon_0,c,D>0$ and $N_0$ such that the following holds for every $N\ge N_0$, uniformly over the measures and relation. Put $\delta=2^{-N}$. Let $\nu,\rho$ be probabilities on $\mathbb R^{k+1}$ whose supports lie in $\overline B(0,L)$ and whose cross-support distances are at least $a$. Assume both have all-scale ball bounds $Kr^s$ for $0<r\le1$. Let $G$ be a Borel pair relation. Suppose its unnormalized forward and reverse directional laws satisfy cap bounds $\delta^{-\varepsilon_0}u^q$ and linear-hyperplane plate bounds $Cu^\zeta$ for every $\delta\le u\le1$, at almost every corresponding pin.
--
--   There is a Borel $B\subset G$ with $(\nu\otimes\rho)(B)\le D\delta^c$ such that both directional laws of $G\setminus B$ give every cap of radius $\delta$ mass at most $\delta^{q+c}$, at almost every corresponding pin. Lean displays the dyadic scale, the uniform threshold, and a deletion constant $D$ distinct from the fixed plate constant $C$, using the paper's null-fiber convention.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem one_scale_improvement {k : ℕ} (hk : 2 ≤ k) (s q ζ L a K C : ℝ)
    (hs : (k:ℝ)-1/2 < s) (hsk : s < k)
    (hq : (k:ℝ)-1 ≤ q) (hqS : q < (k:ℝ)-1/2)
    (hζ : 0 < ζ) (hL : 0 < L) (ha : 0 < a) (hK : 0 < K) (hC : 0 < C) :
    ∃ ε₀ c D : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 < D ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ ν ρ : Measure (Space (k+1)),
        Probability ν → Probability ρ → BoundedSeparated ν ρ L a →
        Frostman ν s K → Frostman ρ s K →
        ∀ G : PairSet (k+1), MeasurableSet G →
          bothCaps ν ρ G q ((mesh N)^(-ε₀)) (mesh N) →
          bothPlates ν ρ G ζ C (mesh N) →
          ∃ B : PairSet (k+1), MeasurableSet B ∧ B ⊆ G ∧
            (ν.prod ρ) B ≤ ENNReal.ofReal (D*(mesh N)^c) ∧
            bothAtRadius ν ρ (G \ B) (mesh N) ((mesh N)^(q+c)) := by sorry
end FalconerPath
