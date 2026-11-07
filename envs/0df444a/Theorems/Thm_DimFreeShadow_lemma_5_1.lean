-- Prove2me | Theorems.Thm_DimFreeShadow_lemma_5_1
-- name    : DimFreeShadow.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:49.055199+00:00
-- url     : https://prove2.me/theorems/2722cbed-c699-40ff-98e4-0584c5c32658
-- title:
--   Lemma 5.1 — finite minimax with attainment
-- statement:
--   Let $L$ be a nonempty compact convex subset of a finite-dimensional real vector space, and let $f_i:L\to\mathbb R$, $i\in I$, be finitely many continuous affine functions, with $I$ nonempty. Then
--
--   $$
--   \min_{N\in L}\max_{i\in I}f_i(N)=\max_{\pi\in\mathcal P(I)}\min_{N\in L}\sum_{i\in I}\pi_if_i(N),
--   $$
--
--   and both extrema are attained. In particular, if each mixed adversary has a response with expected loss at most $q$, one $N$ has every loss at most $q$.
--
--   Applied to the compact convex set of grid-output POVMs, this removes the dependence on the prior.
--
--   Differences from the source:
--   - encoding: a finite-dimensional real vector space → a finite-dimensional real normed space; reason: every such space carries a norm, and all norms give its unique vector topology
--   - encoding: f_i : L → ℝ continuous and affine → f_i : V → ℝ with ContinuousOn on L and the affine identity on L; reason: only the restriction to L matters, and any function on L extends to V
--   - encoding: min max = max min, both attained → a common value v, a point N₀ ∈ L and a law π₀ with: f_i(N₀) ≤ v for all i; every N has some f_i(N) ≥ v; Σ π₀_i f_i(N) ≥ v for all N; every π has some N with Σ π_i f_i(N) ≤ v; reason: these four clauses say exactly that v is the value of both sides and that both extrema are attained, without the junk values of real ⨅ and ⨆
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Lemma 5.1, p.22

import Mathlib

namespace DimFreeShadow

/-- **Lemma 5.1 (finite minimax with attainment)** (arXiv:2608.06345, sha256 a1a42249…,
Lemma 5.1, p.22). Let `L` be a nonempty compact convex subset of a finite-dimensional real
vector space and `f_i : L → ℝ`, `i ∈ I`, finitely many continuous affine functions, `I`
nonempty. Then `min_{N∈L} max_{i∈I} f_i(N) = max_{π∈P(I)} min_{N∈L} Σ_i π_i f_i(N)` (27), both
extrema are attained, and in particular, if each mixed adversary `π` has a response `N ∈ L`
with expected loss at most `q`, one `N ∈ L` has every loss at most `q`.

**Formalization Note** The vector space is a finite-dimensional real normed space (every
finite-dimensional real vector space carries such a norm, and all of them give its unique
vector topology). `f_i` is given on the whole space and only its restriction to `L` matters:
continuity is `ContinuousOn` and affinity is `f(a x + b y) = a f(x) + b f(y)` for `x, y ∈ L`,
`a, b ≥ 0`, `a + b = 1`. `P(I)` is `stdSimplex ℝ I`. (27) with both extrema attained is stated
through a common value `v` without `⨅/⨆`: `N₀ ∈ L` has `max_i f_i(N₀) ≤ v` and every `N ∈ L`
has `max_i f_i(N) ≥ v` (so `v = min_N max_i f_i`, attained at `N₀`); `π₀ ∈ P(I)` has
`Σ_i π₀_i f_i(N) ≥ v` for every `N ∈ L`, and every `π` has some `N ∈ L` with
`Σ_i π_i f_i(N) ≤ v` (so `v = max_π min_N Σ_i π_i f_i(N)`, attained at `π₀`, the inner minimum
at `π₀` being attained at `N₀`). The last clause is the "In particular" sentence. -/
theorem lemma_5_1 {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype I] [Nonempty I] (L : Set V) (hL : L.Nonempty) (hLc : IsCompact L)
    (hLcv : Convex ℝ L) (f : I → V → ℝ) (hfc : ∀ i, ContinuousOn (f i) L)
    (hfa : ∀ i, ∀ x ∈ L, ∀ y ∈ L, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f i (a • x + b • y) = a * f i x + b * f i y) :
    (∃ v : ℝ, ∃ N₀ ∈ L, ∃ π₀ ∈ stdSimplex ℝ I,
      (∀ i, f i N₀ ≤ v) ∧ (∀ N ∈ L, ∃ i, v ≤ f i N) ∧
      (∀ N ∈ L, v ≤ ∑ i, π₀ i * f i N) ∧
      (∀ π ∈ stdSimplex ℝ I, ∃ N ∈ L, ∑ i, π i * f i N ≤ v)) ∧
    ∀ q : ℝ, (∀ π ∈ stdSimplex ℝ I, ∃ N ∈ L, ∑ i, π i * f i N ≤ q) →
      ∃ N ∈ L, ∀ i, f i N ≤ q := by sorry

end DimFreeShadow
