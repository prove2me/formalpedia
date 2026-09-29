-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul
-- name    : Deformation.DieudonneModule.bijective_prod_map_of_bijective_tensorProduct_comul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/d7c7e3b0-d068-507d-865f-91eecb94ce4f
-- title:
--   Additivity of the Dieudonné module along a splitting
-- statement:
--   Fix a prime $p$ and commutative rings $B$, $G^c$, $G^e$ in a single universe, each carrying a bialgebra structure over $\mathbb{Z}/p$. Let $q^c : B \to G^c$, $\pi^e : B \to G^e$ and $\Theta : B \to G^c \otimes_{\mathbb{Z}/p} G^e$ be bialgebra homomorphisms such that $\Theta$ is bijective as a function and, for every $b \in B$, $\Theta(b)$ equals the image of the comultiplication $\Delta b \in B \otimes_{\mathbb{Z}/p} B$ under the algebra homomorphism $q^c \otimes \pi^e$. Here, for a $\mathbb{Z}/p$-bialgebra $A$, [`Deformation.DieudonneModule (ZMod p) p A`](def/Dieudonne_WittHomColimit.html#L234) is the direct limit, over $n$ along the maps induced by the shift $W_n \to W_{n+1}$, of the additive groups `wittHom` of those truncated Witt vectors $x \in W_n(A)$ satisfying $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$, where $\iota_1, \iota_2 : A \to A \otimes_{\mathbb{Z}/p} A$ are the two inclusions; a bialgebra homomorphism $\varphi$ induces the additive map [`Deformation.DieudonneModule.map`](def/Dieudonne_WittHomColimit.html#L380) by functoriality of truncated Witt vectors. The conclusion is that the additive map $z \mapsto \bigl(M(q^c)z,\, M(\pi^e)z\bigr)$ from [`Deformation.DieudonneModule (ZMod p) p B`](def/Dieudonne_WittHomColimit.html#L234) to the product of the corresponding groups for $G^c$ and $G^e$ is bijective.
--
--   This is the additivity of the Dieudonné module functor on a group scheme presented as a product, transported along a given splitting: if $\operatorname{Spec} B \cong \operatorname{Spec} G^c \times \operatorname{Spec} G^e$ via $\Theta$, then $M(B) \cong M(G^c) \times M(G^e)$ by the two induced maps. It is used in the analysis of Honda systems, for the construction of the connected–étale decomposition of the Dieudonné module and for the computation of its rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open MvPowerSeries

universe v

theorem Deformation.DieudonneModule.bijective_prod_map_of_bijective_tensorProduct_comul
    (p : ℕ) [Fact p.Prime]
    (B : Type v) [CommRing B] [Bialgebra (ZMod p) B]
    (Gc Ge : Type v) [CommRing Gc] [Bialgebra (ZMod p) Gc] [CommRing Ge] [Bialgebra (ZMod p) Ge]
    (qc : B →ₐc[ZMod p] Gc) (πe : B →ₐc[ZMod p] Ge) (Θ : B →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hΘ : Function.Bijective Θ)
    (hΘapply : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b)) :
    Function.Bijective fun z : Deformation.DieudonneModule (ZMod p) p B =>
      (Deformation.DieudonneModule.map (ZMod p) p qc z, Deformation.DieudonneModule.map (ZMod p) p πe z) := by sorry
