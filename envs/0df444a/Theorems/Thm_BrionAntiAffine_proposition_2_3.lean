-- Prove2me | Theorems.Thm_BrionAntiAffine_proposition_2_3
-- name    : BrionAntiAffine.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:59.524145+00:00
-- url     : https://prove2.me/theorems/9bbaf8f2-4ba7-45c4-97fd-0ec654316fff
-- title:
--   Proposition 2.3 — anti-affine vector extensions
-- statement:
--   Let $k$ have characteristic $0$ and let $A$ be an abelian variety. There is a universal vector extension
--
--   $$0\to V\to E(A)\to A\to 0,\qquad V=H^1(A,\mathcal O_A)^*,$$
--
--   and any extension $G$ of $A$ by a vector group $U$ fits into a unique diagram (2.4) with classifying map $\gamma:V\to U$. Then:
--
--   (i) $E(A)$ is anti-affine.
--
--   (ii) $G$ is anti-affine if and only if $\gamma$ is surjective. When it is, the subspace invariant of $G$ is the image of the transpose $\gamma^t:U^*\to H^1(A,\mathcal O_A)$.
--
--   (iii) The anti-affine groups over $A$ obtained as vector extensions are classified by the subspaces of the $k$-vector space $H^1(A,\mathcal O_A)$, through $(G,\alpha)\mapsto\ker(\alpha^*)$.
--
--   This is the case of Theorem 2.7 where $G_{\mathrm{aff}}$ is a vector group.
--
--   **Formalization Note** The identification $V=H^1(A,\mathcal O_A)^*$ is the bijection between homomorphisms $\ell:V\to\mathbb G_a$ and classes in $H^1(A,\mathcal O_A)$ given by push-out classes. The transpose sends $\ell$ to the class of $\ell\circ\gamma$.
--
--   Differences from the source:
--   - generalization: E(A) is recalled before the proposition (p.8) → the existence of E, universal, with kernel identified with H¹(A, O_A)^*, is part of the conclusion; reason: keeps (i) and (ii) from being vacuous; the conclusion contains the printed (i), (ii), (iii)
--   - encoding: the kernel H¹(A, O_A)^* of E(A) → a vector group V with ℓ ↦ class of the push-out along ℓ a bijection from homomorphisms V → 𝔾ₐ onto CechH1 A; reason: in characteristic 0 such homomorphisms are the dual of V; this is the classical identification (Serre VII.17)
--   - generalization: (ii) G anti-affine iff γ surjective → adds: if G is anti-affine then vSet αG is the image of γᵗ, ℓ ↦ class of ℓ ∘ γ; reason: connects the map of the printed proof of (iii) to the kernel form used by the goal; dropping it gives the printed statement
--   - encoding: H¹(A, O_A) → Čech cohomology CechH1 A for the cover by all affine opens; reason: A is separated, so the cover is Leray; the same k-vector space
--   - reading: "classified by the subspaces", with no map named → the map (G, α) ↦ vSet α; reason: the proof of (iii) assigns to γ the image of γᵗ, and the added conjunct identifies that image with the kernel
--   - encoding: a bijection on isomorphism classes → clauses (a) each object yields a lattice (and a subspace), (b) every lattice (and subspace) arises, (c) invariants agree iff isomorphic over A; reason: these three say the map on isomorphism classes is well defined, surjective and injective
--   - encoding: a group scheme over A: a connected G with G/Gaff ≃ A → a homomorphism α with IsChevalleyQuotient: faithfully flat quasi-compact, connected affine kernel, and every such β to an abelian variety factors through α; reason: the two are the same data, since a subgroup scheme lies in ker β exactly when β factors through the quotient by it; connectedness of G follows
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Proposition 2.3, p.8, with (2.4); proof of (iii), p.9

import Mathlib
import Definitions.Def_BrionAntiAffine_IsVectorGroup

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Proposition 2.3, Brion, arXiv:0710.5211v3, p.8, with the diagram (2.4); `k` has characteristic `0`
(§2.2). The abelian variety `A` has a universal vector extension `E(A)` with kernel
`H¹(A, 𝒪_A)^*`, and: (i) `E(A)` is anti-affine; (ii) with the notation of (2.4), `G` is anti-affine iff
the classifying map `γ : H¹(A, 𝒪_A)^* → U` is surjective; (iii) the anti-affine groups over `A` obtained
as vector extensions are classified by the subspaces of the `k`-vector space `H¹(A, 𝒪_A)`.

**Formalization Note.** The existence of `E(A)` is recalled on p.8 and is included so that (i) and (ii)
are not vacuous; the identification of its kernel with `H¹(A, 𝒪_A)^*` is the bijection, by
`IsExtensionClass`, between homomorphisms `ℓ : V → 𝔾ₐ` and classes in `H¹(A, 𝒪_A)`. In (iii) the
bijection is stated as clauses (a), (b), (c) for `(G, α) ↦ vSet α`. The conjunct identifying
`vSet αG` with the image of `γᵗ : U^* → H¹(A, 𝒪_A)`, `ℓ ↦ ℓ ∘ γ`, is an addition to the printed
statement: it connects the printed map of the proof of (iii) to the kernel form used by the goal. -/
theorem proposition_2_3 [CharZero k] (A : Sch k) [GrpObj A] (hA : IsAbelianVariety A) :
    (∃ (V E : Sch k) (_ : GrpObj V) (_ : GrpObj E) (iE : V ⟶ E) (βE : E ⟶ A),
      IsUniversalVectorExtension iE βE ∧
      (∀ l : ∀ S : Sch k, (S ⟶ V) → Γ(S.left, ⊤), IsGaHom l → ∃! u : CechH1 A, IsExtensionClass iE βE l u) ∧
      (∀ u : CechH1 A, ∃! l : ∀ S : Sch k, (S ⟶ V) → Γ(S.left, ⊤),
        IsGaHom l ∧ IsExtensionClass iE βE l u) ∧
      IsAntiAffine E ∧
      ∀ (U G : Sch k) [GrpObj U] [GrpObj G] (iG : U ⟶ G) (αG : G ⟶ A) (c : V ⟶ U) (φ : E ⟶ G),
        IsVectorGroup U → IsExactSeq iG αG → FillsDiagram iE βE iG αG c φ →
          (IsAntiAffine G ↔ Surjective c.left) ∧
          (IsAntiAffine G → vSet αG = {u | ∃ l : ∀ S : Sch k, (S ⟶ U) → Γ(S.left, ⊤), IsGaHom l ∧
            IsExtensionClass iE βE (fun S x => l S (x ≫ c)) u})) ∧
    (∀ G : AntiAffineOver A, HasVectorKernel G →
      ∃ W : Submodule k (CechH1 A), (W : Set (CechH1 A)) = vSet G.α) ∧
    (∀ W : Submodule k (CechH1 A),
      ∃ G : AntiAffineOver A, HasVectorKernel G ∧ vSet G.α = (W : Set (CechH1 A))) ∧
    (∀ G G' : AntiAffineOver A, HasVectorKernel G → HasVectorKernel G' →
      (vSet G.α = vSet G'.α ↔ Nonempty (IsoOver G G'))) := by sorry

end BrionAntiAffine
