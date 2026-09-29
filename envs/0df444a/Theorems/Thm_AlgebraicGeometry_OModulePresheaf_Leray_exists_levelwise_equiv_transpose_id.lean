-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.exists_levelwise_equiv_transpose_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/baf1f4d9-d086-59b6-96a8-c48935effafa
-- title:
--   Transposing the Čech–Leray double complex of id_X
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $\pi\colon X\to\operatorname{Spec} R$ a morphism, and let $\mathfrak P,\mathcal W$ be two ordered affine open covers of $X$ (finite index sets carrying a linear order, with affine opens covering $X$). For a cover $K$ write $K.\mathrm{Idx}\,a$ for the strictly monotone maps $\mathrm{Fin}(a+1)\to K.\iota$ and $K.\mathrm{inter}\,\sigma=\bigwedge_j K.U(\sigma j)$. The double complex $\mathtt{LerayDblCpx}\,(\mathbf 1_X)\,\pi\,\mathcal W\,\mathfrak P$ has $(p,q)$-term the product over pairs $(\tau,\sigma)\in\mathcal W.\mathrm{Idx}\,p\times\mathfrak P.\mathrm{Idx}\,q$ of the sections of the unit $\mathcal O$-module presheaf on $\mathfrak P.\mathrm{inter}\,\sigma\wedge(\mathbf 1_X)^{-1}(\mathcal W.\mathrm{inter}\,\tau)$, with the two alternating-sum Čech differentials in the $\mathcal W$- and $\mathfrak P$-directions; likewise with the roles of $\mathfrak P,\mathcal W$ exchanged. The assertion is that there exist $R$-linear isomorphisms $e_{p,q}$ from the $(p,q)$-term of $\mathtt{LerayDblCpx}\,(\mathbf 1_X)\,\pi\,\mathcal W\,\mathfrak P$ to the $(p,q)$-term of $\mathtt{DoubleComplex.transpose}$ of $\mathtt{LerayDblCpx}\,(\mathbf 1_X)\,\pi\,\mathfrak P\,\mathcal W$, i.e. to the $(q,p)$-term of the latter, such that $e$ commutes with the horizontal differentials and with the vertical differentials (checked on elements, the transpose having its differentials interchanged), and such that for every $x$, $\sigma\in\mathfrak P.\mathrm{Idx}\,q$ and $\tau\in\mathcal W.\mathrm{Idx}\,p$ the component $(e_{p,q}x)(\sigma,\tau)$ is the restriction of $x(\tau,\sigma)$ along the inclusion $\mathcal W.\mathrm{inter}\,\tau\wedge(\mathbf 1_X)^{-1}(\mathfrak P.\mathrm{inter}\,\sigma)\le\mathfrak P.\mathrm{inter}\,\sigma\wedge(\mathbf 1_X)^{-1}(\mathcal W.\mathrm{inter}\,\tau)$. No separatedness hypothesis on $\pi$ is required.
--
--   This records the symmetry of the Čech–Leray double complex attached to the identity morphism of $X$ and a pair of ordered affine covers: interchanging the two covers produces the transposed double complex, levelwise and compatibly with both differentials, the isomorphism being pinned down by an explicit restriction formula. It is used in the construction of the edge isomorphisms for the unit $\mathcal O$-module presheaf, being cited by [`AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_levelwise_equiv_transpose_id
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ, (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q ≃ₗ[R]
        (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).C p q,
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e (p + 1) q ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dH p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dH p q (e p q x)) ∧
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e p (q + 1) ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dV p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dV p q (e p q x)) ∧
      ∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q) (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
        (e p q x : OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 q p) (σ, τ) =
          (X.presheaf.map (homOfLE (le_inf
              (inf_le_right.trans (Scheme.Hom.id_preimage (𝔓.inter σ)).le)
              ((Scheme.Hom.id_preimage (𝒲.inter τ)).ge.trans' inf_le_left) :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ OModulePresheaf.Leray.biOpen (𝟙 X) 𝒲 𝔓 p q τ σ)).op).hom
            (x (τ, σ)) := by sorry
