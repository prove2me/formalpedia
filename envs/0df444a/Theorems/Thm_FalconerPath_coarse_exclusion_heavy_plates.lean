-- Prove2me | Theorems.Thm_FalconerPath_coarse_exclusion_heavy_plates
-- name    : FalconerPath.coarse_exclusion_heavy_plates
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:26.936927+00:00
-- url     : https://prove2.me/theorems/7e237f21-c5e8-4432-9b4b-6983501b5dde
-- title:
--   Decreasing coarse filters with directional plate bounds
-- statement:
--   Let $k\ge2$, $k-\tfrac12<s<k$, and $K>0$. Let $\rho_1,\rho_2$ be probabilities on $\mathbb R^{k+1}$ with bounded separated supports, each satisfying $\rho_i(B(z,r))\le Kr^s$ for all centers and $0<r\le1$. Suppose $\rho_1+\rho_2$ gives zero mass to every affine $k$-plane. For every $0<\omega\le1$ there is a decreasing sequence of Borel relations $\Gamma_N\subset\operatorname{supp}\rho_1\times\operatorname{supp}\rho_2$ with $(\rho_1\otimes\rho_2)(\bigcap_N\Gamma_N)>0$.
--
--   There are one translated dyadic grid and a fixed $D\ge0$ such that for every $N$, $\Gamma_N$ is the supported product intersected with a finite union of pairs of depth-$j$ cells for some $j\le\omega N+D$. There are also $\zeta,C>0$, independent of $N$, such that both unnormalized directional laws of $\Gamma_N$ assign mass at most $Cu^\zeta$ to every width-$u$ neighborhood of a linear hyperplane on the sphere, for $2^{-N}\le u\le1$, at almost every corresponding pin. Lean reads the cell-pair equality relative to the supported product and expresses the permitted null-fiber removal almost everywhere.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.3, Lemma 5.9 (Coarse exclusion of heavy plates), label prep:coarse-filter, clauses (i), (ii), and (iii). The paper proves this lemma and cites Shmerkin2023, Appendix B, and Ren2023, Section 7, as antecedents.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem coarse_exclusion_heavy_plates {k : ℕ} (hk : 2 ≤ k) (s K : ℝ)
    (hs : (k:ℝ)-1/2 < s) (hsk : s < k) (hK : 0 < K)
    (ρ₁ ρ₂ : Measure (Space (k+1))) (h₁ : Probability ρ₁) (h₂ : Probability ρ₂)
    (hsep : HasBoundedSeparated ρ₁ ρ₂)
    (hf₁ : Frostman ρ₁ s K) (hf₂ : Frostman ρ₂ s K)
    (hzero : NoAffineMass (ρ₁+ρ₂) k)
    (ω : ℝ) (hω : 0 < ω) (hω₁ : ω ≤ 1) :
    ∃ Γ : ℕ → PairSet (k+1), (∀ N, MeasurableSet (Γ N) ∧
      Γ N ⊆ ρ₁.support ×ˢ ρ₂.support) ∧ Antitone Γ ∧
      0 < (ρ₁.prod ρ₂) (⋂ N, Γ N) ∧
      (∃ v : Space (k+1), ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
        ∃ j : ℕ, (j:ℝ) ≤ ω*N+D ∧
          CoarseCellPairs ρ₁.support ρ₂.support (Γ N) v j) ∧
      ∃ ζ C : ℝ, 0 < ζ ∧ 0 < C ∧ ∀ N,
        bothPlates ρ₁ ρ₂ (Γ N) ζ C (mesh N) := by sorry
end FalconerPath
