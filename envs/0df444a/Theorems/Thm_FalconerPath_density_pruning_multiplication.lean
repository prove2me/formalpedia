-- Prove2me | Theorems.Thm_FalconerPath_density_pruning_multiplication
-- name    : FalconerPath.density_pruning_multiplication
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:37.261333+00:00
-- url     : https://prove2.me/theorems/4bfd595f-3dc5-4bf2-9fba-eefc84a8cf7a
-- title:
--   Density pruning multiplies local fiber estimates
-- statement:
--   Fix an integer $n\ge1$, either the radial test or the full-line test, and constants $L,a,C_1>0$. There is $C_0>0$ such that the following holds for every $C\ge C_0$. Let $\rho$ be a source probability and $\nu$ a finite positive pin measure on $\mathbb R^n$, both with supports in $\overline B(0,L)$. For the radial test require $|x-z|\ge a$ for every cross-support pair. Let $N,J\in\mathbb N$ and let $a_0<\cdots<a_J\le N$ be integer depths in one translated dyadic grid. Let $G$ be a Borel subset of the support product containing no diagonal pair. For each $j<J$, let $E_j$ be Borel with $G\subset E_j$, and let $f_j\ge0$.
--
--   Assume that for every $(x,z)\in G$ and every depth-$a_j$ cell $Q$ containing $z$,
--
--   $$\rho\{z^\prime\in Q:(x,z^\prime)\in E_j,\ T_j(x,z,z^\prime)\}\le f_j\rho(Q).$$
--
--   For the radial test, $T_j$ is $|\pi_x(z^\prime)-\pi_x(z)|\le C2^{-a_{j+1}}$. For the full-line test it is $\operatorname{dist}(z^\prime,x+\mathbb R(z-x))\le C2^{-a_{j+1}}$.
--
--   For every $e>0$ there is a Borel $G^\prime\subset G$ deleting at most $(J+1)2^{-eN}\nu(\mathbb R^n)$ product mass such that for every pin $x\in\mathbb R^n$, every initial depth-$a_0$ cell $Q_0$, and every unit $w$,
--
--   $$\rho\{z\in Q_0:(x,z)\in G^\prime,\ \pi_x(z)\in B(w,C_12^{-a_J})\}\le2^{eNJ}\left(\prod_{j=0}^{J-1}f_j\right)\rho(Q_0).$$
--
--   The Lean statement combines the two versions with a Boolean choice and makes fixed geometry and width thresholds explicit.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 3, Lemma 3.2 (Density pruning and multiplication), label reg:pruning-multiplication, equations labeled reg:local-fibre and reg:multiplied-fibre, and its final full-line variant.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem density_pruning_multiplication {n : ℕ} (hn : 1 ≤ n)
    (lineTest : Bool) (L a C₁ : ℝ) (hL : 0 < L) (ha : 0 < a) (hC₁ : 0 < C₁) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C ≥ C₀,
      ∀ (ρ ν : Measure (Space n)), Probability ρ → FiniteBorel ν →
        ρ.support ⊆ Metric.closedBall 0 L → ν.support ⊆ Metric.closedBall 0 L →
        (lineTest = false → ∀ x ∈ ν.support, ∀ z ∈ ρ.support, a ≤ dist x z) →
        ∀ (N J : ℕ) (depth : ℕ → ℕ),
          (∀ j < J, depth j < depth (j+1)) → depth J ≤ N →
          ∀ (v : Space n) (G : PairSet n) (E : ℕ → PairSet n) (f : ℕ → ℝ),
            MeasurableSet G → G ⊆ ν.support ×ˢ ρ.support →
            (∀ z ∈ G, z.1 ≠ z.2) →
            (∀ j < J, MeasurableSet (E j) ∧ G ⊆ E j ∧ 0 ≤ f j) →
            LocalFiberBounds lineTest ρ G E v depth J f C →
            ∀ e : ℝ, 0 < e → ∃ G' : PairSet n,
              MeasurableSet G' ∧ G' ⊆ G ∧
              (ν.prod ρ) (G \ G') ≤
                ENNReal.ofReal (((J:ℝ)+1)*(scale N)^(-e)) * ν univ ∧
              ∀ (x : Space n) (i : Fin n → ℤ) (w : Space n), w ∈ unitSphere n →
                ρ {z | z ∈ dyadicCell v (depth 0) i ∧ (x,z) ∈ G' ∧
                  radial x z ∈ Metric.ball w (C₁*mesh (depth J))} ≤
                ENNReal.ofReal ((scale N)^(e*J) * ∏ j ∈ Finset.range J, f j) *
                  ρ (dyadicCell v (depth 0) i) := by sorry
end FalconerPath
