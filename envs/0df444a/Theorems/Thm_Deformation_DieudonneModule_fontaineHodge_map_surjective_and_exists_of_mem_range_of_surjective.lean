-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
-- name    : Deformation.DieudonneModule.fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/81f2fc1f-48f5-575b-92cc-b6521e50b57b
-- title:
--   Fontaine's submodule is exact along a Hopf-algebra surjection
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, and let $\mathbb Z/p$ be an $\mathcal O$-algebra whose structure map has kernel exactly the ideal $(p)$. Let $\mathcal R$ and $\mathcal R_1$ be commutative rings carrying cocommutative Hopf algebra structures over $\mathcal O$, each free and finite as an $\mathcal O$-module of rank a power of $p$, and assume the Cartier dual $\mathrm{CartierDual}\,(\mathbb Z/p)\,((\mathbb Z/p)\otimes_{\mathcal O}\mathcal R)$, i.e. the $\mathbb Z/p$-dual of the special fibre of $\mathcal R$, is a local ring. Let $\pi : \mathcal R \to \mathcal R_1$ be a surjective morphism of $\mathcal O$-bialgebras, and assume the Hopf kernel $\mathrm{hopfKer}\,\pi$ — the equaliser of the coaction $(\mathrm{id}\otimes\pi)\circ\Delta$ and $a \mapsto a\otimes 1$ on $\mathcal R$ — is flat over $\mathcal O$. Throughout, for a commutative ring $A$ with bialgebra structure over $\mathbb Z/p$, $\mathrm{DieudonneModule}\,(\mathbb Z/p)\,p\,A$ is the colimit over $n$ of the additive groups $\mathrm{wittHom}\,(\mathbb Z/p)\,p\,n\,A$ of truncated Witt vectors over $A$ that are "grouplike" for comultiplication, transition maps being the shift maps, and $\mathrm{fontaineHodge}\,(\mathbb Z/p)\,p\,\pi'$ is the $\mathbb Z$-submodule of classes admitting, at some level $n$, a representative lying in the subgroup $\mathrm{fontaineKer}\,p\,n\,\pi'$; it is taken with $\pi'$ the right inclusion $A_0 \to (\mathbb Z/p)\otimes_{\mathcal O} A_0$ for $A_0 = \mathcal R_1$, $\mathcal R$ or $\mathrm{hopfKer}\,\pi$, and the maps on Dieudonné modules are those induced functorially by base change of $\pi$, respectively of the inclusion $\mathrm{hopfKerVal}\,\pi$, along $\mathcal O \to \mathbb Z/p$. The conclusion is the conjunction of two assertions: first, every element of $\mathrm{fontaineHodge}$ for $\mathcal R_1$ is the image under the map induced by $\mathrm{id}\otimes\pi$ of some element of $\mathrm{fontaineHodge}$ for $\mathcal R$; second, every element of $\mathrm{fontaineHodge}$ for $\mathcal R$ that lies in the image of the map induced by $\mathrm{id}\otimes\mathrm{hopfKerVal}\,\pi$ is the image of an element of $\mathrm{fontaineHodge}$ for $\mathrm{hopfKer}\,\pi$.
--
--   This is the half concerning Fontaine's submodule $L$ of the exactness of the functor $G \mapsto (L(G), M(G_{\mathbb F_p}))$ on finite flat commutative $p$-group schemes over a base with $\mathcal O/p = \mathbb F_p$, for the closed immersion $G_1 \hookrightarrow G$ dual to $\pi$ with quotient corresponding to $\mathrm{hopfKer}\,\pi$: surjectivity of $L(G) \to L(G_1)$ together with the statement that an element of $L(G)$ coming from $M(G/G_1)$ already comes from $L(G/G_1)$. It feeds the analysis of Honda systems attached to finite flat group schemes, being used by [`Deformation.DieudonneModule.map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer`](thm.html#Deformation.DieudonneModule.map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Deformation.DieudonneModule.fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ)))
    (ℛ₁ : Type v) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] [Coalgebra.IsCocomm 𝓞 ℛ₁]
    [Module.Free 𝓞 ℛ₁] [Module.Finite 𝓞 ℛ₁] (hrank₁ : ∃ a : ℕ, Module.finrank 𝓞 ℛ₁ = p ^ a)
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Function.Surjective π)
    [Module.Flat 𝓞 ↥(HopfAlgebra.hopfKer π)] :
    (∀ z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) y = z) ∧
    (∀ y ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom,
      (∃ x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)) x = y) →
      ∃ x ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            ↥(HopfAlgebra.hopfKer π) →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ↥(HopfAlgebra.hopfKer π)).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)) x = y) := by sorry
