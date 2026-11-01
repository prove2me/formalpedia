-- Prove2me | Theorems.Thm_DRSubmodHull_theorem_7_1_epigraph_convex_hull
-- name    : DRSubmodHull.theorem_7_1_epigraph_convex_hull
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:02.688761+00:00
-- url     : https://prove2.me/theorems/4286d474-560b-4223-9c3c-e35a9c6b3681
-- title:
--   Theorem 7.1 (corrected: f concave along each coordinate) — DR, MIR, box and monotonicity inequalities describe the convex hull of the epigraph
-- statement:
--   Let $\mathcal G=(\mathcal V,\mathcal A)$ be a directed rooted forest on a finite vertex set, $N\subseteq\mathcal V$ the set of integer variables, and $u$ upper bounds with $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ on every arc $(i,j)$. Assume Assumption 1, Property 4.2 and Assumption 2. Let $f:\mathbb R^{\mathcal V}\to\mathbb R$ satisfy $f(0)=0$ and be DR-submodular and concave along each coordinate on the box $[0,u]$. Then
--   $$
--   \mathrm{conv}\big(\mathcal P_f^{\mathcal Z(\mathcal G,u)}\big)=\Big\{(z,w)\in\mathbb R^{\mathcal V}\times\mathbb R:\ z\in\mathcal{CZ},\ \ w\ge\sum_{k=1}^{|\mathcal V|} t(\delta,z)_k\big[f(P(\delta,k))-f(P(\delta,k-1))\big]\ \text{for every valid permutation }\delta\Big\}.
--   $$
--
--   In words: the DR inequalities of all valid permutations, together with the MIR inequalities, the box constraints and the monotonicity constraints that describe $\mathrm{conv}(\mathcal Z(\mathcal G,u))$, fully describe the convex hull of the epigraph of $f$ over the mixed-integer set. The hull is a polyhedron, so minimizing $f$ over $\mathcal Z(\mathcal G,u)$ is equivalent to a linear program over it.
--
--   **Formalization Note** $\mathrm{conv}$ is the convex hull (finite convex combinations), not its closure. The standing conditions, Assumptions 1 and 2 and Property 4.2 are the paper's own hypotheses (pp.4–5, p.8 and the §7 preamble on p.28), not additions.
--
--   Differences from the source:
--   - correction: f DR-submodular → f DR-submodular and concave along each coordinate on [0, u] (IsCoordConcaveOn (Set.Icc 0 u) f); reason: the printed statement is false: one continuous variable, 𝒜 = ∅, u₁ = 2, f = A with A : ℝ → ℝ ℚ-linear, A(1) = 0, A(√2) = 1 satisfies every assumption (f(0) = 0, DR-submodular, Ψ = ∅), the DR inequality reads w ≥ 0, and (2 − √2, −1) lies in the epigraph; the proof of Lemma 3.2 (p.33) passes from midpoint concavity to concavity without regularity, and the added hypothesis is exactly what it claims to derive
--   - reading: f defined and DR-submodular on 𝒳 ⊇ {0 ≤ z ≤ u, z_i ≤ z_j on arcs} (§2) or on a product ∏ᵢ 𝒳ᵢ (§3) → f DR-submodular (and coordinate-concave) on the real box [0, u]; reason: §3's product domain, which every later section uses; Lemma 3.3's coordinate path and the evaluations of f at fractional points in Lemmas 6.8, 6.9 leave the monotone set and the integer lattice
--   - generalization: f : 𝒳 → ℝ DR-submodular on its domain 𝒳 ⊇ [0, u] → f : ℝ^V → ℝ constrained only on [0, u]; reason: Definition 1.1 restricted to a subset of 𝒳 still holds, so every f of the paper satisfies the Lean hypotheses
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: permutations δ = (δ(1), …, δ(|𝒱|)); index 0 for 'no ascendant' with u₀ = z₀ = 0 → δ : Fin |V| ≃ V (Lean position m is the paper's position m + 1); i△(𝒮) : Option V with none ↦ 0; reason: Lean convention; t(δ, z)_k keeps the paper's 1-based k, with t₀ = 1 and t_{|𝒱|+1} = 0
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Theorem 7.1, p.28 (§7 preamble p.28; standing conditions pp.4–5; Assumption 1 and Property 4.2 p.6, standing from p.8; Assumption 2 p.26)

import Mathlib
import Definitions.Def_DRSubmodHull_IsDRSubmodularOn
import Definitions.Def_DRSubmodHull_drRHS

set_option autoImplicit false

namespace DRSubmodHull

/-- **Theorem 7.1 (corrected)** (Yu, Küçükyavuz, *On Constrained Mixed-Integer DR-Submodular
Minimization*, arXiv:2211.07726v2, §7, p.28). All the DR inequalities associated with valid
permutations, along with the MIR inequalities, the box constraints, and the monotonicity
constraints for `conv(𝒵(𝒢, u))`, fully describe `conv(𝒫_f^{𝒵(𝒢,u)})`:
`conv(𝒫_f) = {(z, w) : z ∈ 𝒞𝒵, w ≥ ∑_{k=1}^{|𝒱|} t(δ, z)_k [f(P(δ, k)) − f(P(δ, k − 1))]
for every valid δ}`.

Hypotheses (all the paper's own): `𝒢 = (𝒱, 𝒜)` a directed rooted forest, `u > 0`, `u` integer-valued
on the integer coordinates `N`, `u` monotone along arcs (pp.4–5), `f(0) = 0` (p.5),
Assumption 1 and Property 4.2 (p.8), Assumption 2 (§7 preamble, p.28: "Throughout this section,
we assume that Assumptions 1 and 2 hold"), `f` DR-submodular.

**Formalization Note.** `f : ℝ^V → ℝ` is assumed DR-submodular on the box `[0, u]` (the §3
domain `∏ᵢ 𝒳ᵢ`; any `f` DR-submodular on a larger set is DR-submodular on `[0, u]`; values off
`[0, u]` are irrelevant), with `f(0) = 0` (standing condition, p.5). The hypothesis
`IsCoordConcaveOn (Set.Icc 0 u) f` (concavity along each coordinate on `[0, u]`) is the
correction: without it the printed statement is false (one continuous variable, `u = 2`, `f` a ℚ-linear `A` with `A(1) = 0`,
`A(√2) = 1`: the right-hand set contains only points with `w ≥ 0`, but `(2 − √2, −1)` lies in the
epigraph). `conv` is Mathlib's `convexHull ℝ`, not its closure. -/
theorem theorem_7_1_epigraph_convex_hull {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (hA2 : Assumption2 A N u)
    (f : (V → ℝ) → ℝ) (hf0 : f 0 = 0) (hDR : IsDRSubmodularOn (Set.Icc 0 u) f)
    (hconc : IsCoordConcaveOn (Set.Icc 0 u) f) :
    convexHull ℝ (epigraph A N u f) =
      {p | p.1 ∈ CZ A N u ∧
        ∀ δ : Fin (Fintype.card V) ≃ V, IsValidPerm A N u δ → drRHS A N u f δ p.1 ≤ p.2} := by sorry

end DRSubmodHull
