-- Prove2me | Theorems.Thm_FalconerPath_finite_energy_and_projection
-- name    : FalconerPath.finite_energy_and_projection
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:39.096302+00:00
-- url     : https://prove2.me/theorems/18c5977a-d461-4dca-a276-096151e546de
-- title:
--   Finite energies, compact restrictions, and generic projections
-- statement:
--   Let $\mu$ be a finite positive Borel measure on $\mathbb R^d$ with bounded support. Write $I_t(\mu)=\iint|x-y|^{-t}\,d\mu(x)d\mu(y)$. The following three conclusions hold.
--
--   1. For every real $s$ and $C>0$, an all-scale bound $\mu(B(z,r))\le Cr^s$ for $0<r\le1$ implies $I_t(\mu)<\infty$ for every $0<t<s$.
--   2. For every $t>0$ with $I_t(\mu)<\infty$ and every $\varepsilon>0$, there is a compact $K\subset\operatorname{supp}\mu$ with $\mu(K)\ge\mu(\mathbb R^d)-\varepsilon$, and a constant $C>0$, such that $\mu|_K(B(z,r))\le Cr^t$ for every center and $0<r\le1$.
--   3. For every $t>0$ and integer $m$ with $t<m\le d$ and $I_t(\mu)<\infty$, almost every frame of $m$ independent standard Gaussian vectors in $\mathbb R^d$ spans an $m$-dimensional plane $V$ and satisfies $I_t((P_V)_\#\mu)<\infty$, where $P_V$ is orthogonal projection, with values in the original ambient space.
--
--   The Lean formulation parameterizes Haar-random planes by Gaussian frames and includes their almost sure full rank.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 2.2, Lemma 2.1 (Finite energy and projection), label conv:energy, parts (i), (ii), and (iii). The printed lemma has no bracketed title.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem finite_energy_and_projection {d : ℕ} (μ : Measure (Space d))
    (hfinite : FiniteBorel μ) (hbounded : Bornology.IsBounded μ.support) :
    (∀ s C : ℝ, 0 < C → Frostman μ s C →
      ∀ t : ℝ, 0 < t → t < s → energy t μ < ∞) ∧
    (∀ t : ℝ, 0 < t → energy t μ < ∞ → ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (Space d), IsCompact K ∧ K ⊆ μ.support ∧
        μ univ - ENNReal.ofReal ε ≤ μ K ∧
        ∃ C : ℝ, 0 < C ∧ Frostman (μ.restrict K) t C) ∧
    (∀ (t : ℝ) (m : ℕ), 0 < t → t < m → m ≤ d → energy t μ < ∞ →
      ∀ᵐ v ∂gaussianFrames d m,
        Module.finrank ℝ (framePlane v) = m ∧
        energy t (Measure.map (framePlane v).starProjection μ) < ∞) := by sorry
end FalconerPath
