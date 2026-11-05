-- Prove2me | Theorems.Thm_BrionAntiAffine_proposition_2_1
-- name    : BrionAntiAffine.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:58.661434+00:00
-- url     : https://prove2.me/theorems/cda6e6ad-dd08-4384-972e-0c25d92feace
-- title:
--   Proposition 2.1 — anti-affine semi-abelian varieties
-- statement:
--   Let $A$ be an abelian variety over $k$.
--
--   (i) For an extension (2.1) $1\to T\to G\xrightarrow{\alpha}A\to 0$ with $T$ a torus and character group $\Lambda$, the eigensheaves of (2.2) define a $\Gamma_k$-equivariant homomorphism
--
--   $$c:\Lambda\to A^\vee(k_s),\qquad\lambda\mapsto c(\lambda),$$
--
--   and $G$ is anti-affine if and only if $c$ is injective. When $G$ is anti-affine, the image of $c$ is the lattice invariant $\ker(\alpha_{k_s}^*)$.
--
--   (ii) The isomorphism classes of anti-affine semi-abelian varieties over $A$ correspond bijectively to the sub-$\Gamma_k$-lattices of $A^\vee(k_s)$, through $(G,\alpha)\mapsto\ker(\alpha_{k_s}^*)$.
--
--   This is the case of Theorem 2.7 where $G_{\mathrm{aff}}$ is a torus.
--
--   **Formalization Note** $c$ is existential and is pinned by the eigensheaf property. Equivariance relates $\lambda$ and $\lambda'=\sigma^*\lambda$ along pullback by $\sigma\in\Gamma_k$.
--
--   Differences from the source:
--   - encoding: the map c of (2.3), given by the sheaves L_λ → ∃ c, with IsEigenClass for every λ, range in picZero, and Γk-equivariance; reason: the eigensheaf property determines c(λ) as a class, so this is the printed map
--   - generalization: G anti-affine iff c injective → adds the conjunct: if G is anti-affine then range c = latticeSet α; reason: connects c to the kernel form used by the goal; dropping the conjunct gives the printed statement
--   - encoding: A∨(ks), classes algebraically equivalent to 0 → classes in Pic(A_ks) with t_x^*L ≅ L for all x ∈ A(ks); reason: φ_L vanishes on A(ks), dense in A over the algebraic closure, and Pic(A_ks) injects into Pic of that base change; then Mumford §8
--   - encoding: a sub-Γk-lattice: a free abelian group of finite rank with Γk-action, inside A∨(ks) → a subgroup of Pic(A_ks) inside picZero A, finitely generated, torsion-free, stable under pullback by every σ; reason: finitely generated and torsion-free is free of finite rank; Λ = 0 included
--   - reading: "correspond bijectively", with no map named → the map (G, α) ↦ latticeSet α; reason: the proof of (ii) sends G to the image of c, and the added conjunct identifies that image with the kernel
--   - encoding: a bijection on isomorphism classes → clauses (a) each object yields a lattice (and a subspace), (b) every lattice (and subspace) arises, (c) invariants agree iff isomorphic over A; reason: these three say the map on isomorphism classes is well defined, surjective and injective
--   - encoding: a group scheme over A: a connected G with G/Gaff ≃ A → a homomorphism α with IsChevalleyQuotient: faithfully flat quasi-compact, connected affine kernel, and every such β to an abelian variety factors through α; reason: the two are the same data, since a subgroup scheme lies in ker β exactly when β factors through the quotient by it; connectedness of G follows
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Proposition 2.1, p.7, with (2.1)–(2.3), pp.6–7

import Mathlib
import Definitions.Def_BrionAntiAffine_IsTorus

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Proposition 2.1, Brion, arXiv:0710.5211v3, p.7, with the notation (2.1)–(2.3). Let `A` be an
abelian variety. (i) For an extension `1 → T → G → A → 0` of `A` by a torus `T`, with character group
`Λ`, the eigensheaves `L_λ` of (2.2) define a `Γk`-equivariant homomorphism `c : Λ → A∨(ks)` of (2.3),
and `G` is anti-affine iff `c` is injective. (ii) The isomorphism classes of anti-affine semi-abelian
varieties over `A` correspond bijectively to the sub-`Γk`-lattices of `A∨(ks)`.

**Formalization Note.** In (i) `c` is existential and pinned by the eigensheaf property, so that the
statement is not vacuous. The conjunct `Set.range c = latticeSet α` is an addition to the printed
statement: it connects `c` to the kernel form of the invariant used by the goal. In (ii) the bijection
is stated as clauses (a), (b), (c) for the map `(G, α) ↦ latticeSet α`. -/
theorem proposition_2_1 (A : Sch k) [GrpObj A] (hA : IsAbelianVariety A) :
    (∀ (T G : Sch k) [GrpObj T] [GrpObj G] (i : T ⟶ G) (α : G ⟶ A), IsTorus T → IsExactSeq i α →
      ∃ c : characters T →* Pic (A ⊗ Tks k).left,
        (∀ lam : characters T, IsEigenClass i α lam.1 (c lam)) ∧
        (∀ lam : characters T, c lam ∈ picZero A) ∧
        (∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (lam lam' : characters T),
          lam'.1 = pullUnits (T ◁ galoisMap σ) lam.1 →
            c lam' = Pic.pullback (A ◁ galoisMap σ).left (c lam)) ∧
        (IsAntiAffine G ↔ Function.Injective c) ∧
        (IsAntiAffine G → Set.range c = latticeSet α)) ∧
    (∀ G : AntiAffineOver A, HasTorusKernel G →
      ∃ Λ : Subgroup (Pic (A ⊗ Tks k).left), IsSubGammaLattice A Λ ∧
        (Λ : Set (Pic (A ⊗ Tks k).left)) = latticeSet G.α) ∧
    (∀ Λ : Subgroup (Pic (A ⊗ Tks k).left), IsSubGammaLattice A Λ →
      ∃ G : AntiAffineOver A, HasTorusKernel G ∧
        latticeSet G.α = (Λ : Set (Pic (A ⊗ Tks k).left))) ∧
    (∀ G G' : AntiAffineOver A, HasTorusKernel G → HasTorusKernel G' →
      (latticeSet G.α = latticeSet G'.α ↔ Nonempty (IsoOver G G'))) := by sorry

end BrionAntiAffine
