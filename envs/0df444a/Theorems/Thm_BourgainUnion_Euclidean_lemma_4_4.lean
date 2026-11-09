-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_4_4
-- name    : BourgainUnion.Euclidean.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:44.958421+00:00
-- url     : https://prove2.me/theorems/1702ab4d-7cca-458e-bbf7-566893ee1d53
-- title:
--   Lemma 4.4 — canonical Euclidean elimination
-- statement:
--   Let $G$ be any nonnegatively weighted loopless graph on a finite set $X$, and let $\varnothing\ne A\subseteq X$. The computed graph $G^A$ exists, has nonnegative weights, is uniquely determined by its Dirichlet energies, and is obtained by removing $X\setminus A$ in any order using the update rule of Section 4.2. For every map $f:A\to\ell_2$ the minimum is attained and
--   $$E_{G^A}(f)=\min_{F:X\to\ell_2,\ F|_A=f} E_G(F).$$
--   For every $A\subseteq A'\subseteq X$,
--   $$(G^{A'})^A=G^A.$$
--   Finally, for a fixed partition $U_1,\ldots,U_k$ into nonempty sets, the class $\mathcal D$ of pseudometrics Euclidean on every part, $A=U_i$, and every Euclidean terminal pseudometric $\rho$,
--   $$\operatorname{min-ext}_{\mathcal D}(\rho,G)\le E_{G^A}(\rho^2).$$
--   This supplies the canonical energy-minimizing graph and the full comparison clause, without connectivity or positive-degree assumptions.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: maps defined only on a specified subset → total representatives on the ambient type, constrained only on that subset; reason: every subset map has a total representative by setting it to zero off the subset; those extra values impose no conditions
--   - encoding: a graph on a subset and a sum over unordered pairs → a weight matrix supported on that subset, with half the ordered-pair energy sum; reason: the zero diagonal and symmetry give exactly the same energy, including disconnected and all-zero graphs
--   - encoding: the graph G^A described by its extension-minimum property → the concrete eliminationList matrix, proved to have that property and to be unique; reason: the update rule defines the object independently of the theorem conclusion; isolated vertices are deleted without division
--   - encoding: the least distortion or extension factor, potentially infinite → an infimum in ℝ≥0∞ of finite admissible factors at least one; reason: empty admissible sets give infinity; no real infimum default or unjustified attainment is used; empty and singleton spaces have the conventional factor one
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 15, Lemma 4.4, equations (6)–(7)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 4.4: computed graph, uniqueness, all orders, attained minimum, composition, and (4). -/
theorem lemma_4_4 {X : Type*} [Fintype X] [DecidableEq X]
    (G : ClusterDecomp.WGraph X) (hG : Loopless G) (A : Finset X) (hA : A.Nonempty) :
    DirichletGraph G.w (canonical G.w A) A ∧
    (∀ h : X → X → ℝ, DirichletGraph G.w h A → h = canonical G.w A) ∧
    (∀ order : List X, order.Perm (Finset.univ \ A).toList →
      eliminateList G.w Finset.univ order = canonical G.w A) ∧
    (∀ A' : Finset X, A ⊆ A' → canonical (canonical G.w A') A = canonical G.w A) ∧
    (∀ (k : ℕ) (U : Fin k → Set X) (i : Fin k), Partition U → U i = (A : Set X) →
      ∀ ρ : X → X → ℝ, RawEuclidean ρ (A : Set X) →
        minExt U A ρ G.w ≤ ENNReal.ofReal (energy (canonical G.w A) ρ A)) := by sorry

end BourgainUnion.Euclidean
