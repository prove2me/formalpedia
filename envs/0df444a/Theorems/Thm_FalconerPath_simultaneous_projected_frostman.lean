-- Prove2me | Theorems.Thm_FalconerPath_simultaneous_projected_frostman
-- name    : FalconerPath.simultaneous_projected_frostman
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:42.259204+00:00
-- url     : https://prove2.me/theorems/164d3973-d6da-42b4-b7fb-c092b3984094
-- title:
--   Simultaneous projected Frostman bounds
-- statement:
--   Let $d\ge2$ and let $E\subset\mathbb R^d$ be compact with $\dim_H E>S=d/2$. First, $E$ carries a probability $\rho$ with an all-scale ball bound of some exponent $s>S$ and constant $C>0$.
--
--   Second, take any such $\rho,s,C$. Let $n_0,\ldots,n_J$ be any finite nonincreasing list of integer dimensions, with $n_0=d$ and every $n_i>S$. For every $t$ with $S<t<s$ and $t<n_i$ for all $i$, there are continuous linear maps $P_i:\mathbb R^d\to\mathbb R^{n_i}$ satisfying $P_iP_i^*=I$, with $P_0$ an isometry and $P_{i+1}=Q_iP_i$ for orthogonal surjections $Q_i$. Every unrestricted projected law $(P_i)_\#\rho$ has finite $t$-energy. If $k\ge2$, $d=2k-1$, and $\rho$ vanishes on all affine $k$-planes, then each projected law with $n_i=k+1$ vanishes on every affine hyperplane.
--
--   There are also a compact $K\subset E$ with $\rho(K)>0$ and constants $\chi,C^\prime>0$ such that $\eta=\rho|_K/\rho(K)$ and every $(P_i)_\#\eta$ satisfy the same all-scale bound $C^\prime r^{S+\chi}$ for every center and $0<r\le1$. The Lean version quantifies the finite dimension list and exposes a compatible choice of projections and one common original compact restriction.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.2, Lemma 5.6 (Simultaneous projected Frostman bounds), label prep:projections.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem simultaneous_projected_frostman {d : ℕ} (hd : 2 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E)
    (hdim : (d : ℝ≥0∞)/2 < dimH E) :
    (∃ ρ : Measure (Space d), Probability ρ ∧ Carried ρ E ∧
      ∃ s C : ℝ, (d:ℝ)/2 < s ∧ 0 < C ∧ Frostman ρ s C) ∧
    (∀ (ρ : Measure (Space d)) (s C : ℝ), Probability ρ → Carried ρ E →
      (d:ℝ)/2 < s → 0 < C → Frostman ρ s C →
      ∀ (J : ℕ) (dims : Fin (J+1) → ℕ), dims 0 = d →
        (∀ i : Fin J, dims i.succ ≤ dims i.castSucc) →
        (∀ i, (d:ℝ)/2 < (dims i:ℝ)) →
        ∀ t : ℝ, (d:ℝ)/2 < t → t < s → (∀ i, t < (dims i:ℝ)) →
        ∃ P : (i : Fin (J+1)) → Space d →L[ℝ] Space (dims i),
          CompatibleProjections dims P ∧
          (∀ i, energy t (Measure.map (P i) ρ) < ∞) ∧
          (∀ k : ℕ, 2 ≤ k → d = 2*k-1 → NoAffineMass ρ k →
            ∀ i, dims i = k+1 → NoAffineMass (Measure.map (P i) ρ) (dims i-1)) ∧
          ∃ K : Set (Space d), IsCompact K ∧ K ⊆ E ∧ 0 < ρ K ∧
            ∃ χ C' : ℝ, 0 < χ ∧ 0 < C' ∧
              Frostman (normalizedRestriction ρ K) ((d:ℝ)/2+χ) C' ∧
              (∀ i, Frostman (Measure.map (P i) (normalizedRestriction ρ K))
                ((d:ℝ)/2+χ) C')) := by sorry
end FalconerPath
