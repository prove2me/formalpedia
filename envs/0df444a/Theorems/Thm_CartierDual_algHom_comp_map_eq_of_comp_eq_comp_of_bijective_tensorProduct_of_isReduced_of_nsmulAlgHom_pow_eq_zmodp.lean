-- Prove2me | Theorems.Thm_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
-- name    : CartierDual.algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/8cfcb2ab-b787-56bc-b054-03c4daf8d245
-- title:
--   Cartier dual characters determined on the connected factor
-- statement:
--   Fix a prime $p$, and let $B$, $G_c$, $G_e$ be commutative rings carrying cocommutative Hopf algebra structures over $\mathbb{Z}/p$ that are finite as $\mathbb{Z}/p$-modules. Let $q_c : B \to G_c$, $\pi_e : B \to G_e$ and $\Theta : B \to G_c \otimes_{\mathbb{Z}/p} G_e$ be bialgebra homomorphisms with $q_c$ and $\pi_e$ surjective and $\Theta$ bijective, and assume $\Theta(b) = (q_c \otimes \pi_e)(\Delta b)$ for all $b \in B$, where $\Delta$ is the comultiplication of $B$. Assume further that for some $N$ the $p^N$-th convolution power of the identity of $G_e$ (the algebra endomorphism [`PDivisibleGroup.Hopf.nsmulAlgHom`](def/PDivisibleGroup_Basic.html#L16) at $p^N$) equals the counit of $G_e$ followed by the structure map $\mathbb{Z}/p \to G_e$, and that $G_e$ is reduced. Let $\kappa$ be a reduced commutative $\mathbb{Z}/p$-algebra and $\chi$ a $\mathbb{Z}/p$-algebra homomorphism from the Cartier dual $\operatorname{CartierDual}(\mathbb{Z}/p, B)$, i.e. the $\mathbb{Z}/p$-linear dual of $B$ with its convolution algebra structure, to $\kappa$. Then for any two bialgebra endomorphisms $g_1, g_2$ of $B$ satisfying $q_c \circ g_1 = q_c \circ g_2$ as algebra maps, the composites of the Cartier transposes [`CartierDual.map g₁`](def/HopfAlgebra_CartierDualMap.html#L102), [`CartierDual.map g₂`](def/HopfAlgebra_CartierDualMap.html#L102) with $\chi$ agree.
--
--   This is the statement that a $\kappa$-valued point of the Cartier dual of a finite commutative $\mathbb{F}_p$-group scheme, for $\kappa$ reduced of characteristic $p$, depends only on the connected factor of the given splitting of $B$ into a connected and an étale part. It is used in the comparison of Cartier transposes of endomorphisms in the treatment of Cartier duality for $p$-divisible groups, through [`PDivisibleGroup.CartierDuality.forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp`](thm.html#PDivisibleGroup.CartierDuality.forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
    (qc : B →ₐc[ZMod p] Gc) (πe : B →ₐc[ZMod p] Ge) (Θ : B →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe) (hΘ : Function.Bijective Θ)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge) (Coalgebra.comul (R := ZMod p) b))

    (N : ℕ) (hkill : PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) Ge (p ^ N) =
      (Algebra.ofId (ZMod p) Ge).comp (Bialgebra.counitAlgHom (ZMod p) Ge))
    (hGe : IsReduced Ge)
    (κ : Type) [CommRing κ] [Algebra (ZMod p) κ] [IsReduced κ]
    (χ : CartierDual (ZMod p) B →ₐ[ZMod p] κ)
    (g₁ g₂ : B →ₐc[ZMod p] B)
    (hg : (qc : B →ₐ[ZMod p] Gc).comp (g₁ : B →ₐ[ZMod p] B) = (qc : B →ₐ[ZMod p] Gc).comp (g₂ : B →ₐ[ZMod p] B)) :
    χ.comp (CartierDual.map g₁ : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B) =
      χ.comp (CartierDual.map g₂ : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B) := by sorry
