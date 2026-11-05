-- Prove2me | Theorems.Thm_BrionAntiAffine_classification
-- name    : BrionAntiAffine.classification
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:00.859534+00:00
-- url     : https://prove2.me/theorems/97924624-1e48-4f4d-9fdf-bab1bc2f765b
-- title:
--   Theorem 2.7 — classification of anti-affine groups over an abelian variety
-- statement:
--   Let $k$ be a field with separable closure $k_s$ and Galois group $\Gamma_k$, and let $A$ be an abelian variety over $k$.
--
--   (i) If $k$ has positive characteristic, the isomorphism classes of anti-affine groups over $A$ correspond bijectively to the sub-$\Gamma_k$-lattices $\Lambda\subset A^\vee(k_s)$.
--
--   (ii) If $k$ has characteristic $0$, the isomorphism classes of anti-affine groups over $A$ correspond bijectively to the pairs $(\Lambda,V)$, where $\Lambda$ is as in (i) and $V$ is a subspace of $H^1(A,\mathcal O_A)$.
--
--   The correspondence sends $(G,\alpha)$ to
--
--   $$\Lambda=\ker\bigl(\alpha_{k_s}^*:\mathrm{Pic}(A_{k_s})\to\mathrm{Pic}(G_{k_s})\bigr),\qquad V=\ker\bigl(\alpha^*:H^1(A,\mathcal O_A)\to H^1(G,\mathcal O_G)\bigr).$$
--
--   Bijectivity is expressed by three clauses:
--
--   1. the invariants of every $(G,\alpha)$ are a lattice (and a subspace);
--   2. every lattice (and subspace) arises;
--   3. the invariants agree exactly when the groups are isomorphic over $A$.
--
--   This reduces the structure of anti-affine groups to that of abelian varieties.
--
--   **Formalization Note** $k$ is any field, perfect or not, and $A$ has any dimension. $G$ is not assumed smooth, connected or commutative.
--
--   Differences from the source:
--   - reading: "correspond bijectively", with no map named → the map (G, α) ↦ (ker of α_ks^* on Pic(A_ks), ker of α^* on H¹(A, O_A)), through latticeSet and vSet; reason: the proof sends G to the image of c for G/U and of γᵗ for G/T; Propositions 2.10 and 2.11 identify these with kernels of pull-back; a bare bijection would be a statement about cardinalities
--   - encoding: a group scheme over A: a connected G with G/Gaff ≃ A → a homomorphism α with IsChevalleyQuotient: faithfully flat quasi-compact, connected affine kernel, and every such β to an abelian variety factors through α; reason: the two are the same data, since a subgroup scheme lies in ker β exactly when β factors through the quotient by it; connectedness of G follows
--   - encoding: A∨(ks), classes algebraically equivalent to 0 → classes in Pic(A_ks) with t_x^*L ≅ L for all x ∈ A(ks); reason: φ_L vanishes on A(ks), dense in A over the algebraic closure, and Pic(A_ks) injects into Pic of that base change; then Mumford §8
--   - encoding: H¹(A, O_A) → Čech cohomology CechH1 A for the cover by all affine opens; reason: A is separated, so the cover is Leray; the same k-vector space
--   - encoding: a sub-Γk-lattice: a free abelian group of finite rank with Γk-action, inside A∨(ks) → a subgroup of Pic(A_ks) inside picZero A, finitely generated, torsion-free, stable under pullback by every σ; reason: finitely generated and torsion-free is free of finite rank; Λ = 0 included
--   - reading: "In positive characteristics" → CharP k p with p prime, for an arbitrary field; reason: Section 2.3 and Proposition 2.2 carry no perfectness hypothesis; Section 2.4 is the first to assume it
--   - encoding: a bijection on isomorphism classes → clauses (a) each object yields a lattice (and a subspace), (b) every lattice (and subspace) arises, (c) invariants agree iff isomorphic over A; reason: these three say the map on isomorphism classes is well defined, surjective and injective
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Theorem 2.7, p.11

import Mathlib
import Definitions.Def_BrionAntiAffine_IsSubGammaLattice
import Definitions.Def_BrionAntiAffine_CechH1

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- **Theorem 2.7**, Brion, arXiv:0710.5211v3, p.11. Let `A` be an abelian variety over a field `k`.
(i) In positive characteristics, the isomorphism classes of anti-affine groups over `A` correspond
bijectively to the sub-`Γk`-lattices `Λ ⊂ A∨(ks)`. (ii) In characteristic `0`, the isomorphism classes
of anti-affine groups over `A` correspond bijectively to the pairs `(Λ, V)`, where `Λ` is as in (i) and
`V` is a subspace of `H¹(A, 𝒪_A)`.

**Formalization Note.** The theorem names no map; a bare bijection would be a statement about
cardinalities. The correspondence is `(G, α) ↦ latticeSet α = ker(α_ks^* on Pic)` and
`(G, α) ↦ vSet α = ker(α^* on H¹)`, and "correspond bijectively" is stated as three clauses: (a) the
invariants of each `(G, α)` are a lattice (and a subspace); (b) every lattice (and subspace) arises;
(c) the invariants agree exactly when the groups are isomorphic over `A`. `k` is any field, perfect or
not. -/
theorem classification (A : Sch k) [GrpObj A] (hA : IsAbelianVariety A) :
    (∀ p : ℕ, p.Prime → CharP k p →
      (∀ G : AntiAffineOver A,
        ∃ Λ : Subgroup (Pic (A ⊗ Tks k).left), IsSubGammaLattice A Λ ∧
          (Λ : Set (Pic (A ⊗ Tks k).left)) = latticeSet G.α) ∧
      (∀ Λ : Subgroup (Pic (A ⊗ Tks k).left), IsSubGammaLattice A Λ →
        ∃ G : AntiAffineOver A, latticeSet G.α = (Λ : Set (Pic (A ⊗ Tks k).left))) ∧
      (∀ G G' : AntiAffineOver A,
        latticeSet G.α = latticeSet G'.α ↔ Nonempty (IsoOver G G'))) ∧
    (CharZero k →
      (∀ G : AntiAffineOver A,
        (∃ Λ : Subgroup (Pic (A ⊗ Tks k).left), IsSubGammaLattice A Λ ∧
          (Λ : Set (Pic (A ⊗ Tks k).left)) = latticeSet G.α) ∧
        ∃ V : Submodule k (CechH1 A), (V : Set (CechH1 A)) = vSet G.α) ∧
      (∀ (Λ : Subgroup (Pic (A ⊗ Tks k).left)) (V : Submodule k (CechH1 A)),
        IsSubGammaLattice A Λ →
          ∃ G : AntiAffineOver A, latticeSet G.α = (Λ : Set (Pic (A ⊗ Tks k).left)) ∧
            vSet G.α = (V : Set (CechH1 A))) ∧
      (∀ G G' : AntiAffineOver A,
        (latticeSet G.α = latticeSet G'.α ∧ vSet G.α = vSet G'.α) ↔ Nonempty (IsoOver G G'))) := by sorry

end BrionAntiAffine
