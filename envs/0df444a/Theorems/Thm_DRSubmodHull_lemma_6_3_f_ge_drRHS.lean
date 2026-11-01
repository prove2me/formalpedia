-- Prove2me | Theorems.Thm_DRSubmodHull_lemma_6_3_f_ge_drRHS
-- name    : DRSubmodHull.lemma_6_3_f_ge_drRHS
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:28:05.066525+00:00
-- url     : https://prove2.me/theorems/7b9ae370-0c14-4dd0-bcde-3efda0c18122
-- title:
--   Lemma 6.3 (corrected: f concave along each coordinate) — $f(\bar z)$ dominates the DR right-hand side of Algorithm 2's output
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold. The function $f:\mathbb R^{\mathcal V}\to\mathbb R$ satisfies $f(0)=0$ and is DR-submodular and concave along each coordinate on the box $[0,u]$.
--
--   Let $\bar z\in\mathrm{conv}(\mathcal Z(\mathcal G,u))$ and let $\tau$ be a permutation returned by Algorithm 2 on $\bar z$. Then
--   $$
--   f(\bar z)\;\ge\;\sum_{k=1}^{|\mathcal V|} t(\tau,\bar z)_k\,\big[f(P(\tau,k))-f(P(\tau,k-1))\big].
--   $$
--
--   The DR inequality of the permutation chosen for $\bar z$ thus holds at $(\bar z,f(\bar z))$; this is the step that reduces validity of a DR inequality to its validity at extreme points (Proposition 6.4).
--
--   Differences from the source:
--   - correction: f DR-submodular → f DR-submodular and concave along each coordinate on [0, u] (IsCoordConcaveOn (Set.Icc 0 u) f); reason: the printed statement is false: one continuous variable, 𝒜 = ∅, u₁ = 2, f = A with A : ℝ → ℝ ℚ-linear, A(1) = 0, A(√2) = 1 satisfies every assumption (f(0) = 0, DR-submodular, Ψ = ∅), the DR inequality reads w ≥ 0, and (2 − √2, −1) lies in the epigraph; the proof of Lemma 3.2 (p.33) passes from midpoint concavity to concavity without regularity, and the added hypothesis is exactly what it claims to derive
--   - reading: f defined and DR-submodular on 𝒳 ⊇ {0 ≤ z ≤ u, z_i ≤ z_j on arcs} (§2) or on a product ∏ᵢ 𝒳ᵢ (§3) → f DR-submodular (and coordinate-concave) on the real box [0, u]; reason: §3's product domain, which every later section uses; Lemma 3.3's coordinate path and the evaluations of f at fractional points in Lemmas 6.8, 6.9 leave the monotone set and the integer lattice
--   - generalization: f : 𝒳 → ℝ DR-submodular on its domain 𝒳 ⊇ [0, u] → f : ℝ^V → ℝ constrained only on [0, u]; reason: Definition 1.1 restricted to a subset of 𝒳 still holds, so every f of the paper satisfies the Lean hypotheses
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: permutations δ = (δ(1), …, δ(|𝒱|)); index 0 for 'no ascendant' with u₀ = z₀ = 0 → δ : Fin |V| ≃ V (Lean position m is the paper's position m + 1); i△(𝒮) : Option V with none ↦ 0; reason: Lean convention; t(δ, z)_k keeps the paper's 1-based k, with t₀ = 1 and t_{|𝒱|+1} = 0
--   - reading: 'the output' of Algorithm 2, which breaks ties arbitrarily → every δ satisfying IsPermFinderOutput (every tie-break); reason: the paper fixes no tie-break, so its claim is about each possible output; this is the stronger of the two readings
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Lemma 6.3, p.23 (proof p.37)

import Mathlib
import Definitions.Def_DRSubmodHull_IsDRSubmodularOn
import Definitions.Def_DRSubmodHull_IsPermFinderOutput

set_option autoImplicit false

namespace DRSubmodHull

/-- **Lemma 6.3 (corrected)** (Yu, Küçükyavuz, arXiv:2211.07726v2, §6, p.23). For any
`z̄ ∈ conv(𝒵(𝒢, u))`, let `τ ∈ 𝔖(𝒱)` be the corresponding output from Algorithm 2. Then
`f(z̄) ≥ ∑_{k=1}^{|𝒱|} t(τ, z̄)_k [f(P(τ, k)) − f(P(τ, k − 1))]`.

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8).

**Formalization Note.** `f : ℝ^V → ℝ` is assumed DR-submodular on the box `[0, u]` (the §3
domain `∏ᵢ 𝒳ᵢ`; any `f` DR-submodular on a larger set is DR-submodular on `[0, u]`; values off
`[0, u]` are irrelevant), with `f(0) = 0` (standing condition, p.5). The hypothesis
`IsCoordConcaveOn (Set.Icc 0 u) f` (concavity along each coordinate on `[0, u]`) is the
correction: without it the printed statement is false (one continuous variable, `u = 2`, `f` a ℚ-linear `A` with `A(1) = 0`,
`A(√2) = 1`, `z̄ = 2 − √2`). "The output" is every output of Algorithm 2 (every tie-break). -/
theorem lemma_6_3_f_ge_drRHS {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (f : (V → ℝ) → ℝ) (hf0 : f 0 = 0) (hDR : IsDRSubmodularOn (Set.Icc 0 u) f)
    (hconc : IsCoordConcaveOn (Set.Icc 0 u) f)
    (zbar : V → ℝ) (hz : zbar ∈ convexHull ℝ (Zset A N u))
    (τ : Fin (Fintype.card V) ≃ V) (hτ : IsPermFinderOutput A N u zbar τ) :
    drRHS A N u f τ zbar ≤ f zbar := by sorry

end DRSubmodHull
