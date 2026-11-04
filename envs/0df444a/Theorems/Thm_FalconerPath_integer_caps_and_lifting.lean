-- Prove2me | Theorems.Thm_FalconerPath_integer_caps_and_lifting
-- name    : FalconerPath.integer_caps_and_lifting
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:38.061991+00:00
-- url     : https://prove2.me/theorems/803b894b-b83a-4a3c-8ed7-78dd386fcc70
-- title:
--   Integer cap bounds and lifting through orthogonal projections
-- statement:
--   For a relation $G$, its directional laws are $(\pi_x)_\#(\rho|_{G_x})$ and $(\pi_y)_\#(\nu|_{G^y})$, without fiber normalization. Bounds in both orientations mean bounds at almost every pin for the corresponding marginal. Two assertions hold.
--
--   1. For every integer $h\ge1$, let $\nu,\rho$ be probabilities on $\mathbb R^{h+1}$ with bounded separated supports. Suppose $p>1$ and $L>0$, and suppose both full radial laws have jointly measurable nonnegative surface densities with $p$th power integrals at most $L$ at every support pin. For every $e>0$ there exist $C>0$ and $N_0$ such that for every $N\ge N_0$ there is a Borel $B_N\subset\operatorname{supp}\nu\times\operatorname{supp}\rho$ with product mass at most $C2^{-Ne(p-1)/2}$. On the complementary supported relation, both directional laws give every radius-$u$ cap mass at most $2^{eN}u^h$ for $2^{-N}\le u\le1$.
--   2. For every $1\le m\le d$, let $P:\mathbb R^d\to\mathbb R^m$ be a continuous linear map with $PP^*=I$. Let $\nu,\rho$ be probabilities whose original and projected support pairs are bounded and separated. There is a fixed $C_0>0$ such that for every Borel relation $G$ in the projected product and every $q\ge0$, $K>0$, $0<\delta\le1$, cap bounds $Ku^q$ in both projected orientations for $\delta\le u\le1$ imply cap bounds $C_0K(1+C_0)^q u^q$ in both original orientations on $(P\times P)^{-1}(G)$ for the same radii.
--
--   The Lean formulation separates the two quantified assertions and displays the lifting constant.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.2, Lemma 5.8 (Integer caps and lifting), label prep:integer-caps, first paragraph for integer caps and second paragraph for lifting.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem integer_caps_and_lifting :
    (∀ (h : ℕ), 1 ≤ h → ∀ (ν ρ : Measure (Space (h+1))),
      Probability ν → Probability ρ → HasBoundedSeparated ν ρ →
      ∀ p L : ℝ, 1 < p → 0 < L → UniformRadialLp ν ρ p L →
      ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ∃ B : PairSet (h+1), MeasurableSet B ∧ B ⊆ ν.support ×ˢ ρ.support ∧
          (ν.prod ρ) B ≤ ENNReal.ofReal
            (C * (scale N) ^ (-e*(p-1)/2)) ∧
          bothCaps ν ρ ((ν.support ×ˢ ρ.support) \ B)
            h ((scale N)^e) (mesh N)) ∧
    (∀ (d m : ℕ), 1 ≤ m → m ≤ d →
      ∀ P : Space d →L[ℝ] Space m, OrthogonalSurjection P →
      ∀ ν ρ : Measure (Space d), Probability ν → Probability ρ →
        HasBoundedSeparated ν ρ →
        HasBoundedSeparated (Measure.map P ν) (Measure.map P ρ) →
        ∃ C : ℝ, 0 < C ∧ ∀ (G : PairSet m) (q K δ : ℝ),
          MeasurableSet G → 0 ≤ q → 0 < K → 0 < δ → δ ≤ 1 →
          bothCaps (Measure.map P ν) (Measure.map P ρ) G q K δ →
          bothCaps ν ρ ((fun z : Space d × Space d => (P z.1,P z.2)) ⁻¹' G)
            q (C * K * (1+C)^q) δ) := by sorry
end FalconerPath
