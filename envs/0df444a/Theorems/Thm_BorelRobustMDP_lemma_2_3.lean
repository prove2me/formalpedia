-- Prove2me | Theorems.Thm_BorelRobustMDP_lemma_2_3
-- name    : BorelRobustMDP.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:49.011018+00:00
-- url     : https://prove2.me/theorems/9b729812-e762-4c42-8c4f-7bd13c62684c
-- title:
--   Lemma 2.3 — $\mathcal Q_n$ is separable metrizable, and compact Borel if weak* closed
-- statement:
--   Let $n\in\{1,\dots,N\}$, let $P_n$ be separable, and let the ambiguity set $\mathcal Q_n\subseteq\mathcal M^q(P_n)$ be norm bounded. Then $\mathcal Q_n$ with the weak* topology $\sigma(L^q,L^p)$ is a separable metrizable space. If $\mathcal Q_n$ is also weak* closed, then it is a compact Borel space.
--
--   This makes $\mathcal Q_n$ a measurable space to which selection theorems apply.
--
--   **Formalization Note.** A compact Borel space is stated as compact and Polish.
--
--   Differences from the source:
--   - encoding: σ(L^q, L^p) on the densities 𝒬_n^d and its Borel σ-algebra → the topology on 𝒬_n induced by Q ↦ ∫ f dQ for f ∈ L^p(P_n), with borel of it; weak* closed means closed in this topology on 𝓜^q(P_n); reason: ∫ f dQ = E[f dQ/dP_n], and 𝓜^q(P_n) is weak* closed in L^q, so these are the same notions; no Lp–Lq duality is needed to state them
--   - encoding: compact Borel space → CompactSpace and PolishSpace; reason: a compact metrizable space is Polish
--   - reading: norm-bounded → ‖dQ/dP_n‖_{L^q} ≤ K for a given K; reason: this is the meaning used in the proof, p.23
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Lemma 2.3, p.4; proof p.23

import Mathlib
import Definitions.Def_BorelRobustMDP_AmbiguityFamily

open MeasureTheory

namespace BorelRobustMDP

universe v

/-- Lemma 2.3 (Bäuerle & Glauner, arXiv:2007.13103v1, p.4; proof p.23). If `𝒬_n` is norm bounded and
`P_n` separable, then `𝒬_n` with the weak* topology is a separable metrizable space, and if `𝒬_n`
is weak* closed, it is a compact Borel space.

**Formalization Note.** `n ∈ {1, …, N}`, and separability of `P_n` is a field of the family. A compact
Borel space is a compact Polish space: a compact metrizable space is Polish, and conversely. -/
theorem lemma_2_3 {Z : Type v} [MeasurableSpace Z] {N : ℕ} (𝔸 : AmbiguityFamily Z N) (n : ℕ)
    (hn₁ : 1 ≤ n) (hnN : n ≤ N) (K : ℝ) (hK : 𝔸.NormBounded n K) :
    TopologicalSpace.MetrizableSpace (𝔸.Amb n) ∧ TopologicalSpace.SeparableSpace (𝔸.Amb n) ∧
      (𝔸.WeakStarClosed n → CompactSpace (𝔸.Amb n) ∧ PolishSpace (𝔸.Amb n)) := by sorry

end BorelRobustMDP
