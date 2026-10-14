-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_sections_sub_of_isAffineOpen_sup_of_isInvertible
-- name    : AlgebraicGeometry.Scheme.Modules.exists_sections_sub_of_isAffineOpen_sup_of_isInvertible
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T18:39:14.205251+00:00
-- url     : https://prove2.me/theorems/75f3cb3f-f298-49b6-998a-cfd1d5e3bf1e
-- title:
--   Restriction differences for an invertible sheaf are surjective on an affine union
-- statement:
--   Let $X$ be a scheme, let $M$ be an invertible $\mathcal O_X$-module, and let $U,V\subseteq X$ be open subsets whose union is affine. Every section $s\in\Gamma(U\cap V,M)$ can be expressed as a difference of restrictions:
--
--   $$\exists s_0\in\Gamma(U,M),\ \exists s_1\in\Gamma(V,M),\qquad
--   s_1|_{U\cap V}-s_0|_{U\cap V}=s.$$
--
--   Equivalently, the restriction-difference map
--
--   $$\Gamma(U,M)\oplus\Gamma(V,M)\longrightarrow\Gamma(U\cap V,M)$$
--
--   is surjective. Thus the degree-one Cech group for this two-open cover of the affine open $U\cup V$ vanishes. The individual opens and their intersection are not required to be affine. This local exactness statement supplies sections used in comparisons between different covers.
--
--   **Formalization Note.** The conclusion uses the actual additive groups of sections and the presheaf restriction maps along the two inclusions. No base ring, structure morphism, smoothness, properness, or dimension assumption is part of the statement.
-- source:
--   Consequence of Stacks Project, Lemma 30.2.2, Tag 01XB (https://stacks.math.columbia.edu/tag/01XB), and the Mayer-Vietoris sequence, Lemma 20.8.2, Tag 01EB (https://stacks.math.columbia.edu/tag/01EB). Restrict the invertible, hence quasi-coherent, sheaf to the affine open W = U union V. Affine vanishing gives H^1(W,M) = 0. Exactness of Mayer-Vietoris then makes the difference of section restrictions onto Gamma(U intersection V,M). Reversing the source convention for the sign preserves surjectivity. The two component opens and their intersection need not be affine. This is a consequence in terms of sections, not a literal transcription of either cited lemma.

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Opposite
universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_sections_sub_of_isAffineOpen_sup_of_isInvertible
    {X : Scheme.{u}} (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U V : X.Opens) (hUV : IsAffineOpen (U ⊔ V))
    (s : Γ(M, U ⊓ V)) :
    ∃ s₀ : Γ(M, U), ∃ s₁ : Γ(M, V),
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s₁ -
        M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s₀ = s := by
  sorry
