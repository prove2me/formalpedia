-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
-- name    : AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/73bc5ac8-094e-56e0-93f5-26ac178f7405
-- title:
--   Refinement induces isomorphisms on Čech cohomology of mathcal O_X
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $\pi \colon X \to \operatorname{Spec} R$ a separated morphism. Let $\mathfrak P$ and $\mathcal W$ be ordered affine covers of $X$, each given by a finite linearly ordered index type together with affine opens indexed by it whose supremum is $\top$, and let $\lambda \colon \mathcal W.\iota \to \mathfrak P.\iota$ satisfy $\mathcal W.U\,w \le (\mathbf 1_X)^{-1}(\mathfrak P.U\,(\lambda w))$ for all $w$. Write $\mathcal O$ for the presheaf of $R$-modules `OModulePresheaf.unit π`, $U \mapsto \Gamma(X,U)$ with the $R$-algebra structure coming from $\pi$, and let its Čech cochains on a cover $K$ in degree $i$ be the product of $\Gamma(X, \bigcap_j K.U(s_j))$ over strictly increasing $(i+1)$-tuples $s$. Then there exist an $R$-linear isomorphism $e_0$ from $\ker(d_{\mathfrak P}^0)$ to $\ker(d_{\mathcal W}^0)$ and, for every $n \in \mathbb N$, an $R$-linear isomorphism $e_n$ from $\ker(d_{\mathfrak P}^{n+1})/\operatorname{im}(d_{\mathfrak P}^{n})$ to $\ker(d_{\mathcal W}^{n+1})/\operatorname{im}(d_{\mathcal W}^{n})$, both pinned to the alternating pullback `OModulePresheaf.unitPullback` along $(\mathbf 1_X, \lambda)$ (restriction of sections twisted by the sign of the sorting permutation, and $0$ when $\lambda \circ s$ fails to be injective): $e_0 z$ has underlying $0$-cochain the pullback of $z$, and for each $n$ and each $z \in \ker(d_{\mathfrak P}^{n+1})$ the pullback of $z$ lies in $\ker(d_{\mathcal W}^{n+1})$ and $e_n$ sends the class of $z$ to the class of that pullback.
--
--   This is the independence of Čech cohomology of the structure sheaf on the chosen finite ordered affine cover of a separated scheme, in a pinned form: the comparison isomorphisms are not merely asserted to exist but are identified on cocycles with the alternating refinement pullback. It is used downstream for statements comparing cocycles and coboundaries across covers, for instance that a difference of two pullbacks of a cocycle is a coboundary, and in the Künneth-type injectivity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    ∃ (e₀ : ↥((OModulePresheaf.unit π).H0 𝔓) ≃ₗ[R] ↥((OModulePresheaf.unit π).H0 𝒲))
      (e : ∀ n : ℕ, (OModulePresheaf.unit π).HSucc 𝔓 n ≃ₗ[R] (OModulePresheaf.unit π).HSucc 𝒲 n),
      (∀ z : ↥((OModulePresheaf.unit π).H0 𝔓),
        ((e₀ z : ↥((OModulePresheaf.unit π).H0 𝒲)) : (OModulePresheaf.unit π).cochain 𝒲 0) =
          OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝔓 (n + 1)))),
        ∃ hz : OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit π).d 𝒲 (n + 1)),
          e n (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨_, hz⟩) := by sorry
