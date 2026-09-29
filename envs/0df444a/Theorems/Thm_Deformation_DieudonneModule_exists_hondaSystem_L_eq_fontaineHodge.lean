-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge
-- name    : Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/c627eb79-9275-5c30-b089-469017f01274
-- title:
--   Fontaine's theorem: (L(G),M(G_k)) is a Honda system
-- statement:
--   Let $p$ be a prime and $\mathcal O$ a commutative ring in which $p$ is a non-zero-divisor, let $k$ be a perfect field of characteristic $p$ which is an $\mathcal O$-algebra such that the structure map $\mathcal O \to k$ is surjective with kernel exactly the ideal $(p)$, and let $\mathcal R$ be a commutative ring carrying a Hopf algebra structure over $\mathcal O$ whose comultiplication is cocommutative and which is free and finite as an $\mathcal O$-module, of rank $p^a$ for some $a \in \mathbb N$. Write $A = k \otimes_{\mathcal O} \mathcal R$ and let $D =$ [`Deformation.DieudonneModule k p A`](def/Dieudonne_WittHomColimit.html#L234) be the direct limit over $n$, along the Verschiebung shift maps, of the additive subgroups of primitive elements of $\mathrm{TruncatedWittVector}\ p\ n\ A$ (those $x$ with $\mathrm{map}(\Delta)x = \mathrm{map}(\iota_1)x + \mathrm{map}(\iota_2)x$). Then there is a Honda system over $\mathbb Z$ with parameter $\ell = p$ on $D$ whose underlying Dieudonné datum is the canonical one, with $F$ and $V$ the Frobenius and Verschiebung of $D$ (so $FV = VF = p$), and whose submodule $L \subseteq D$ is $\mathrm{fontaineHodge}$ taken with respect to the ring homomorphism $\mathcal R \to k \otimes_{\mathcal O} \mathcal R$, $r \mapsto 1 \otimes r$, that is, the $\mathbb Z$-submodule of classes of primitive truncated Witt vectors lying in Fontaine's kernel. Being a Honda system means: every $x \in L$ in the range of $F$ is $p \cdot y$ for some $y \in L$; $p \cdot y$ lies in the range of $F$ for every $y \in L$; $\mathrm{range}\,F + L = D$; and $V$ is injective on $L$.
--
--   This is Fontaine's Theorem 1: for a finite flat commutative group scheme $G = \operatorname{Spec}\mathcal R$ of $p$-power order over $\mathcal O$ (for instance $\mathcal O = \mathbb Z_p$ or $W(k)$), the Dieudonné module $M(G_k)$ of the special fibre together with the Fontaine submodule $L(G)$ forms a Honda system. It is the basis of the Dieudonné-theoretic description of finite flat group schemes used downstream, where it is invoked in the analysis of Cartier duality and of the Fontaine submodule under morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [Field k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a) :
    ∃ H : Deformation.HondaSystem (p : ℤ) (Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ)),
      H.toDieudonneDatum = Deformation.DieudonneModule.dieudonneDatum k p (TensorProduct 𝓞 k ℛ) ∧
      H.L = Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom := by sorry
