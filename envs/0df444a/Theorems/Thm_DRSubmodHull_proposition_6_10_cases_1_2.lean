-- Prove2me | Theorems.Thm_DRSubmodHull_proposition_6_10_cases_1_2
-- name    : DRSubmodHull.proposition_6_10_cases_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:17.992596+00:00
-- url     : https://prove2.me/theorems/16fbb270-73d0-4b88-bd54-401a18ca56bd
-- title:
--   Proposition 6.10 (corrected: f concave along each coordinate) — DR inequalities are valid at the points $P(\mathcal S)$ in cases (1) and (2)
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold. The function $f:\mathbb R^{\mathcal V}\to\mathbb R$ satisfies $f(0)=0$ and is DR-submodular and concave along each coordinate on the box $[0,u]$.
--
--   Assume case (1) or case (2) of p.24: either $\Psi=\emptyset$, or $\Psi\ne\emptyset$ and $0<u_\psi<1$ for every $\psi\in\Psi$. Let $\delta$ be a valid permutation. Then for every $\mathcal S\subseteq\mathcal V$,
--   $$
--   f(P(\mathcal S))\;\ge\;\sum_{k=1}^{|\mathcal V|} t(\delta,P(\mathcal S))_k\,\big[f(P(\delta,k))-f(P(\delta,k-1))\big],
--   $$
--   that is, the DR inequality associated with $\delta$ is valid at $[P(\mathcal S),f(P(\mathcal S))]$.
--
--   Differences from the source:
--   - correction: f DR-submodular → f DR-submodular and concave along each coordinate on [0, u] (IsCoordConcaveOn (Set.Icc 0 u) f); reason: the printed statement is false: 𝒱 = {1, 2}, arc (1, 2), both variables continuous, u = (1, √2), f(z) = A(z₂) with A : ℝ → ℝ ℚ-linear, A(1) = 0, A(√2) = 1 (DR-submodular, f(0) = 0, Ψ = ∅); for 𝒮 = {1} and the valid δ = (2, 1), f(P(𝒮)) = A(1) = 0 while the DR right-hand side is (1/√2)·A(√2) = 1/√2
--   - reading: f defined and DR-submodular on 𝒳 ⊇ {0 ≤ z ≤ u, z_i ≤ z_j on arcs} (§2) or on a product ∏ᵢ 𝒳ᵢ (§3) → f DR-submodular (and coordinate-concave) on the real box [0, u]; reason: §3's product domain, which every later section uses; Lemma 3.3's coordinate path and the evaluations of f at fractional points in Lemmas 6.8, 6.9 leave the monotone set and the integer lattice
--   - generalization: f : 𝒳 → ℝ DR-submodular on its domain 𝒳 ⊇ [0, u] → f : ℝ^V → ℝ constrained only on [0, u]; reason: Definition 1.1 restricted to a subset of 𝒳 still holds, so every f of the paper satisfies the Lean hypotheses
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: permutations δ = (δ(1), …, δ(|𝒱|)); index 0 for 'no ascendant' with u₀ = z₀ = 0 → δ : Fin |V| ≃ V (Lean position m is the paper's position m + 1); i△(𝒮) : Option V with none ↦ 0; reason: Lean convention; t(δ, z)_k keeps the paper's 1-based k, with t₀ = 1 and t_{|𝒱|+1} = 0
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Proposition 6.10, p.24 (cases (1)–(3) p.24)

import Mathlib
import Definitions.Def_DRSubmodHull_IsDRSubmodularOn
import Definitions.Def_DRSubmodHull_drRHS

set_option autoImplicit false

namespace DRSubmodHull

/-- **Proposition 6.10 (corrected)** (Yu, Küçükyavuz, arXiv:2211.07726v2, §6.1, p.24). Let `δ` be a
valid permutation ("We consider any valid `δ ∈ 𝔖(𝒱)`", p.24). The DR inequality associated with
`δ` is valid at every `[P(𝒮), f(P(𝒮))]`, `𝒮 ⊆ 𝒱`, in cases (1) and (2), where (p.24)
case (1) is `Ψ = ∅` and case (2) is `Ψ ≠ ∅` with `0 < u_ψ < 1` for every `ψ ∈ Ψ`.

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8).

**Formalization Note.** `f : ℝ^V → ℝ` is assumed DR-submodular on the box `[0, u]` (the §3
domain `∏ᵢ 𝒳ᵢ`; any `f` DR-submodular on a larger set is DR-submodular on `[0, u]`; values off
`[0, u]` are irrelevant), with `f(0) = 0` (standing condition, p.5). The hypothesis
`IsCoordConcaveOn (Set.Icc 0 u) f` (concavity along each coordinate on `[0, u]`) is the
correction: without it the printed statement is false (`𝒱 = {1, 2}`, arc `(1, 2)`, both continuous, `u = (1, √2)`, `f(z) = A(z₂)` with
`A` ℚ-linear, `A(1) = 0`, `A(√2) = 1`, `𝒮 = {1}`, `δ = (2, 1)`: `f(P(𝒮)) = 0 < 1/√2`). -/
theorem proposition_6_10_cases_1_2 {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (f : (V → ℝ) → ℝ) (hf0 : f 0 = 0) (hDR : IsDRSubmodularOn (Set.Icc 0 u) f)
    (hconc : IsCoordConcaveOn (Set.Icc 0 u) f)
    (hcase : Psi A N u = ∅ ∨
      ((Psi A N u).Nonempty ∧ ∀ ψ ∈ Psi A N u, 0 < u ψ ∧ u ψ < 1))
    (δ : Fin (Fintype.card V) ≃ V) (hδ : IsValidPerm A N u δ) (S : Finset V) :
    drRHS A N u f δ (Ppt A N u S) ≤ f (Ppt A N u S) := by sorry

end DRSubmodHull
