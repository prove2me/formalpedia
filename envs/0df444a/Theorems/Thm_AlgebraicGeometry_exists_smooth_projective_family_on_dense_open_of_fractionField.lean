-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_family_on_dense_open_of_fractionField
-- name    : AlgebraicGeometry.exists_smooth_projective_family_on_dense_open_of_fractionField
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T14:42:29.825888+00:00
-- url     : https://prove2.me/theorems/a82deebd-f054-4a9f-bb40-7b01fbae3379
-- title:
--   Smooth projective generic fibres spread over a dense open of a prescribed affine base
-- statement:
--   Let $B$ be an integral domain and let $E$ be its actual fraction field. Let $C$ be a smooth projective $E$-scheme, equipped with a closed immersion into $\mathbb P^n_E$.
--
--   There are a nonzero $s\in B$, an injective $B$-algebra homomorphism $\gamma:B[1/s]\to E$, a closed subscheme $Y\hookrightarrow\mathbb P^n_{B[1/s]}$, and a dense open $U\subset\operatorname{Spec}B[1/s]$ such that the restricted family
--   $$Y_U\longrightarrow U$$
--   is smooth and proper. The actual map $\operatorname{Spec}E\to\operatorname{Spec}B[1/s]$ induced by $\gamma$ factors through $U$, and $C$ is its exact pullback:
--   $$\begin{matrix}
--   C&\longrightarrow&Y_U\\
--   \downarrow&&\downarrow\\
--   \operatorname{Spec}E&\longrightarrow&U.
--   \end{matrix}$$
--   The top left scheme is the given $C$, its structure map is the one specified by its projective embedding, and the bottom map has exactly the prescribed composite to $\operatorname{Spec}B[1/s]$. No replacement by an abstractly isomorphic fraction field is made. The projective ambient model $Y$ is retained. The result holds in arbitrary universes and in arbitrary characteristic, without a noetherian hypothesis on $B$ or a dimension bound on $C$.
--
--   This supplies the smooth open family needed after constructing a normal projective base for a finite generic field extension in the Philippon alteration branch. The theorem does not extend a covering morphism to another scheme or construct a semistable compactification or a global smooth alteration.
-- source:
--   Auxiliary spreading construction for the Philippon generic-curve alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Uses the Proved noetherian approximation of flat projective subschemes https://prove2.me/theorems/44445023-0444-5411-b136-0fd554f8e11d , base change of projective embeddings https://prove2.me/theorems/899d38bc-8ead-534b-ac8b-ae36d35999c7 , and flat-base-change descent of the smooth locus https://prove2.me/theorems/dd990c97-2f4d-55b4-9879-54c6e7ff5f23 . The affine fraction-field base is available from https://prove2.me/theorems/a2fa0ad5-6962-47c5-9e21-5fc176c6d9cb . This result proves spreading over a smooth open family; semistable reduction and global alteration remain separate.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_family_on_dense_open_of_fractionField
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (Y : Scheme.{u})
          (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (Localization.Away s))), IsClosedImmersion j ∧
          ∃ U : (Spec (.of (Localization.Away s))).Opens,
            Dense (U : Set (Spec (.of (Localization.Away s)))) ∧
            ∃ (bU : Spec (.of E) ⟶ U)
              (gU : C ⟶ ((j ≫ ProjSpace.π (Localization.Away s) n) ⁻¹ᵁ U)),
              bU ≫ U.ι = Spec.map (CommRingCat.ofHom γ.toRingHom) ∧
              IsPullback gU (ι ≫ ProjSpace.π E n)
                ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) bU ∧
              Smooth ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) ∧
              IsProper ((j ≫ ProjSpace.π (Localization.Away s) n) ∣_ U) := by sorry
