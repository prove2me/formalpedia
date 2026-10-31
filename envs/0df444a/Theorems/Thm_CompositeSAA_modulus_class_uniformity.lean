-- Prove2me | Theorems.Thm_CompositeSAA_modulus_class_uniformity
-- name    : CompositeSAA.modulus_class_uniformity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:37.858994+00:00
-- url     : https://prove2.me/theorems/62f99f08-793b-4479-9bd1-6e048deef1aa
-- title:
--   Proof of Theorem 4(b), p.8 — functions with a common modulus of continuity form a $P$-uniformity class
-- statement:
--   Let $P$ and $Q_N$ ($N\in\mathbb N$) be probability measures on $\mathbb R^m$ concentrated on a set $\mathcal X$, such that $Q_N\to P$ weakly and
--
--   $$
--   \int\|x\|\,Q_N(dx)\to\int\|x\|\,P(dx),
--   $$
--
--   all these integrals being finite. Let $(G_i)_{i\in\iota}$ be real functions that admit a common modulus of continuity $w$ on the closed convex hull $\operatorname{conv}(\mathcal X)$ and are bounded at some point $x_0\in\mathcal X$. Then
--
--   $$
--   \sup_{i\in\iota}\Bigl|\int G_i\,dQ_N-\int G_i\,dP\Bigr|\to0 .
--   $$
--
--   Applied to the components $\mathbf f_i(u,\eta,\cdot)$ of the composite model this gives $\tilde\beta(Q^j_N,P)\to0$, the uniform convergence of the level integrals that Theorem 3 needs.
--
--   Differences from the source:
--   - generalization: the class $\tilde{\mathfrak F}$, whose functions $\mathbf f_i(u,\eta,\cdot)$, $(u,\eta)\in\mathcal U\times I$, admit the moduli $w_1,\dots,w_d$ → any family with a common modulus $w$, bounded at one point of $\mathcal X$; reason: $\tilde{\mathfrak F}$ is an instance with $w=\max_\ell w_\ell$ (p.7), bounded at $\bar x$ by continuity on the compact $\mathcal U\times I$.
--   - generalization: weak convergence in $\mathcal P(\mathcal X)$ → weak convergence of the measures on $\mathbb R^m$ (bounded continuous test functions on $\mathbb R^m$); reason: the former implies the latter.
--   - encoding: "$\lim_N\sup_{1\le j\le k+1}\tilde\beta(Q^j_N,P)=0$" → one sequence $Q_N$, in $\varepsilon$-eventually form; reason: the finitely many sequences are handled one at a time; same instances.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 4(b), pp.7–8

import Mathlib
import Definitions.Def_CompositeSAA_IsModulus

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 4(b), p.8: "`𝔉̃` is a
`P`-uniformity class".

Let `P` and `Q_N` be probability measures on `ℝ^m` concentrated on `𝒳`, with `Q_N → P` weakly and
`∫ ‖x‖ dQ_N → ∫ ‖x‖ dP`, all these integrals finite. Let `(G_i)` be a family of real functions
with a common modulus of continuity `w` on the closed convex hull `conv(𝒳)`, bounded at some
point `x₀ ∈ 𝒳`. Then `sup_i |∫ G_i dQ_N − ∫ G_i dP| → 0`.

**Formalization Note**
1. The paper's `𝔉̃` (p.5) has finitely many moduli `w_1, …, w_d`; it is the case of this
   statement with `w = max_ℓ w_ℓ` (as on p.7) and the family of components `𝐟_i(u, η, ·)`,
   `(u, η) ∈ 𝒰 × I`, which is bounded at `x₀` by continuity on the compact `𝒰 × I`.
2. Weak convergence is written out with bounded continuous test functions on `ℝ^m`; the
   supremum is written in `ε`-eventually form. -/
theorem modulus_class_uniformity {m : ℕ} {ι : Type*} (𝒳 : Set (EuclideanSpace ℝ (Fin m)))
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (Q : ℕ → Measure (EuclideanSpace ℝ (Fin m))) [∀ N, IsProbabilityMeasure (Q N)]
    (hP𝒳 : ∀ᵐ x ∂P, x ∈ 𝒳) (hQ𝒳 : ∀ N, ∀ᵐ x ∂(Q N), x ∈ 𝒳)
    (hweak : ∀ g : EuclideanSpace ℝ (Fin m) →ᵇ ℝ,
      Tendsto (fun N => ∫ x, g x ∂(Q N)) atTop (𝓝 (∫ x, g x ∂P)))
    (hPmom : Integrable (fun x => ‖x‖) P) (hQmom : ∀ N, Integrable (fun x => ‖x‖) (Q N))
    (hmom : Tendsto (fun N => ∫ x, ‖x‖ ∂(Q N)) atTop (𝓝 (∫ x, ‖x‖ ∂P)))
    (G : ι → EuclideanSpace ℝ (Fin m) → ℝ) (w : ℝ → ℝ) (hw : IsModulus w)
    (hG : ∀ i, ∀ x ∈ closedConvexHull ℝ 𝒳, ∀ x' ∈ closedConvexHull ℝ 𝒳,
      |G i x - G i x'| ≤ w ‖x - x'‖)
    (hbdd : ∃ x₀ ∈ 𝒳, BddAbove (Set.range fun i => |G i x₀|)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ i, |∫ x, G i x ∂(Q N) - ∫ x, G i x ∂P| ≤ ε := by sorry

end CompositeSAA
