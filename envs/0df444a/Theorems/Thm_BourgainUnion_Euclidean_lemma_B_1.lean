-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_B_1
-- name    : BourgainUnion.Euclidean.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:54.094563+00:00
-- url     : https://prove2.me/theorems/041fffe5-301c-4736-8b5c-cadbb464c67c
-- title:
--   Lemma B.1 — explicit direct-sum bound
-- statement:
--   Let $X=A\sqcup B$ be a finite pseudometric space with both parts nonempty, and let $f_A:A\to\ell_2$ and $f_B:B\to\ell_2$ be isometries. Take $t,s\ge1$ and $0<v\le(s+1)^2$. Suppose $f_A$ extends to $F_A:X\to\ell_2$ with factor $t$ on pairs within $B$ and factor $s$ on crossing pairs, while $f_B$ extends to $F_B$ with factor $t$ within $A$ and factor $s$ on crossing pairs. Then
--   $$c_2(X)^2\le\max\{1+t^2+v,\ 2s^2+2v\}\,\frac{(s+1)^2+v}{2v}.$$
--   All four pairwise bounds and both extension identities are required; no convex-hull condition is added. This is the explicit two-set distortion bound independent of the unspecified collapse constants.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: maps defined only on a specified subset → total representatives on the ambient type, constrained only on that subset; reason: every subset map has a total representative by setting it to zero off the subset; those extra values impose no conditions
--   - encoding: the least distortion or extension factor, potentially infinite → an infimum in ℝ≥0∞ of finite admissible factors at least one; reason: empty admissible sets give infinity; no real infimum default or unjustified attainment is used; empty and singleton spaces have the conventional factor one
--   - encoding: finite vertex sets and decompositions Y=A⊔B → a Fintype ambient type, a Finset A, and B=univ\A; reason: no vertices are identified at distance zero, and both empty B and nonempty A have the source values
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 31, Lemma B.1

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_ExtensionModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma B.1: both isometries, both extension families, and the entire squared bound. -/
theorem lemma_B_1 {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
    (A : Finset X) (hA : A.Nonempty) (hB : (Finset.univ \ A).Nonempty)
    (fA fB FA FB : X → H2)
    (hisoA : ∀ x ∈ A, ∀ y ∈ A, dist (fA x) (fA y) = dist x y)
    (hisoB : ∀ x ∈ Finset.univ \ A, ∀ y ∈ Finset.univ \ A,
      dist (fB x) (fB y) = dist x y)
    (hextA : Set.EqOn FA fA (A : Set X))
    (hextB : Set.EqOn FB fB (↑(Finset.univ \ A) : Set X))
    (t s v : ℝ) (ht : 1 ≤ t) (hs : 1 ≤ s) (hv : 0 < v) (hvcap : v ≤ (s+1)^2)
    (hFA : LipOn t FA (↑(Finset.univ \ A) : Set X))
    (hFB : LipOn t FB (A : Set X))
    (hcrossA : ∀ a ∈ A, ∀ b ∈ Finset.univ \ A, dist (FA a) (FA b) ≤ s*dist a b)
    (hcrossB : ∀ a ∈ A, ∀ b ∈ Finset.univ \ A, dist (FB a) (FB b) ≤ s*dist a b) :
    (c2 X)^2 ≤ ENNReal.ofReal (max (1+t^2+v) (2*s^2+2*v) * ((s+1)^2+v)/(2*v)) := by sorry

end BourgainUnion.Euclidean
