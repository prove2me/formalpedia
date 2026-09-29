-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct
-- name    : Deformation.DieudonneModule.exists_addEquiv_prod_apply_eq_map_of_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/f3e0f974-3e8e-531d-8bc3-5e9f6c902a1b
-- title:
--   Additivity of the Dieudonné module on a tensor product
-- statement:
--   Let $p$ be a prime and let $B_1,B_2$ be commutative rings carrying bialgebra structures over $\mathbb{Z}/p$. The assertion is the existence of four bialgebra maps over $\mathbb{Z}/p$ — $i_1\colon B_1\to B_1\otimes_{\mathbb{Z}/p}B_2$, $i_2\colon B_2\to B_1\otimes_{\mathbb{Z}/p}B_2$, $q_1\colon B_1\otimes_{\mathbb{Z}/p}B_2\to B_1$ and $q_2\colon B_1\otimes_{\mathbb{Z}/p}B_2\to B_2$ — such that, as algebra maps, $i_1$ and $i_2$ are `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`, while $q_1(x\otimes y)=\varepsilon(y)\cdot x$ and $q_2(x\otimes y)=\varepsilon(x)\cdot y$ with $\varepsilon$ the counit; and, moreover, the existence of an isomorphism $e$ of additive groups from $\mathrm{DieudonneModule}(\mathbb{Z}/p,p,B_1\otimes_{\mathbb{Z}/p}B_2)$ — the direct limit over $n$, along the shift maps, of the additive groups of those truncated Witt vectors $x$ of length $n$ over the bialgebra which satisfy $W_n(\Delta)(x)=W_n(\iota_1)(x)+W_n(\iota_2)(x)$ — onto the product of the corresponding groups for $B_1$ and $B_2$, with the three properties: $e(z)=(\mathrm{map}\,q_1(z),\mathrm{map}\,q_2(z))$ for all $z$; $e^{-1}(m_1,m_2)=\mathrm{map}\,i_1(m_1)+\mathrm{map}\,i_2(m_2)$; and $e$ intertwines the Frobenius operators and the Verschiebung operators on the two sides, componentwise.
--
--   This is the additivity of the contravariant Dieudonné functor $M=\varinjlim_n\operatorname{Hom}(-,W_n)$ on commutative affine group schemes over $\mathbb{F}_p$: for a product of group schemes, restriction along the two unit sections splits $M$ as a direct sum, compatibly with $F$ and $V$. It is used in the project to reduce statements about Dieudonné modules and Cartier duals of a bialgebra that decomposes as a tensor product to the two factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe v

theorem Deformation.DieudonneModule.exists_addEquiv_prod_apply_eq_map_of_tensorProduct
    (p : ℕ) [Fact p.Prime]
    (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂] [Bialgebra (ZMod p) B₁] [Bialgebra (ZMod p) B₂] :
    ∃ (i₁ : B₁ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂) (i₂ : B₂ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂)
      (q₁ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₁) (q₂ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₂),
      (i₁ : B₁ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeLeft ∧
      (i₂ : B₂ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeRight ∧
      (∀ x y, q₁ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) y • x) ∧
      (∀ x y, q₂ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) x • y) ∧
      ∃ e : Deformation.DieudonneModule (ZMod p) p (B₁ ⊗[ZMod p] B₂) ≃+
          Deformation.DieudonneModule (ZMod p) p B₁ × Deformation.DieudonneModule (ZMod p) p B₂,
        (∀ z, e z = (Deformation.DieudonneModule.map (ZMod p) p q₁ z,
          Deformation.DieudonneModule.map (ZMod p) p q₂ z)) ∧
        (∀ m₁ m₂, e.symm (m₁, m₂) = Deformation.DieudonneModule.map (ZMod p) p i₁ m₁ +
          Deformation.DieudonneModule.map (ZMod p) p i₂ m₂) ∧
        (∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.frobenius (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.frobenius (ZMod p) p B₂ (e z).2)) ∧
        (∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.verschiebung (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.verschiebung (ZMod p) p B₂ (e z).2)) := by sorry
