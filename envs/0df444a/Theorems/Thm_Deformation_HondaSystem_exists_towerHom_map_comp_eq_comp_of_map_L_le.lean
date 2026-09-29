-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le
-- name    : Deformation.HondaSystem.exists_towerHom_map_comp_eq_comp_of_map_L_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/39f2422a-47b2-5923-b1d0-cb2aaee4439b
-- title:
--   Morphisms of Honda systems come from p-divisible towers
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, $\mathbf Z/p$ is an $\mathcal O$-algebra whose structure map has kernel $(p)$, and $\mathcal O$ is $(p)$-adically complete. Fix $r$ and a Honda system $H_1$ on $\mathcal O^r$ for $\ell=p$: $\mathcal O$-linear $F,V$ with $F\circ V=V\circ F=p\cdot\mathrm{id}$ together with a submodule $L$ satisfying Fontaine's four axioms ($x\in L\cap\operatorname{range}F$ implies $x=p y$ with $y\in L$; $p y\in\operatorname{range}F$ for $y\in L$; $\operatorname{range}F+L=\top$; $V$ injective on $L$). Fix also a tower $L_\bullet$ of cocommutative $\mathcal O$-Hopf algebras, finite and free as modules, with surjective $\mathcal O$-bialgebra transitions $t_v\colon L_{v+1}\to L_v$, $\operatorname{finrank}L_v=p^{vr}$, $\ker t_v$ the image of the augmentation ideal of $L_{v+1}$ under multiplication by $p^v$, and with local Cartier dual of each special fibre $\mathbf Z/p\otimes_{\mathcal O}L_v$. Assume given additive surjections $\pi_v\colon\mathcal O^r\to M(\mathbf Z/p\otimes L_v)$ onto the Dieudonné modules, with kernel $p^v\mathcal O^r$, intertwining $F$ and $V$ with Frobenius and Verschiebung, carrying $L$ onto the Fontaine–Hodge subgroup attached to $L_v\to\mathbf Z/p\otimes L_v$, and compatible with the transitions. Assume the same data $(r',H_2,L'_\bullet,t'_\bullet,\pi'_\bullet)$ for a second tower. Let $\varphi\colon\mathcal O^{r'}\to\mathcal O^r$ be $\mathcal O$-linear with $\varphi\circ F_2=F_1\circ\varphi$, $\varphi\circ V_2=V_1\circ\varphi$ and $\varphi(L_2)\subseteq L_1$. Then there are $\mathcal O$-bialgebra maps $f_v\colon L'_v\to L_v$ with $t_v\circ f_{v+1}=f_v\circ t'_v$ and such that the induced map on Dieudonné modules of the special fibres satisfies $M(f_v)\circ\pi'_v=\pi_v\circ\varphi$ for all $v$.
--
--   This is the fullness half of Fontaine's classification of unipotent $p$-divisible groups over $\mathbf Z_p$ by Honda systems, stated relative to given level-by-level identifications of Dieudonné theory with a free Honda system so that it can be combined with the existence half. It is used in the construction of a $p$-divisible tower with prescribed Honda system, [`Deformation.exists_pDivisibleTower_ker_eq_map_bijective_map_comp_mem_fontaineKer_of_isLocalRing_cartierDual_zmodp`](thm.html#Deformation.exists_pDivisibleTower_ker_eq_map_bijective_map_comp_mem_fontaineKer_of_isLocalRing_cartierDual_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Deformation.HondaSystem.exists_towerHom_map_comp_eq_comp_of_map_L_le
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (L : ℕ → Type u) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v))))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)))
    (hπs : ∀ v, Function.Surjective (π v))
    (hπk : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) =
      Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x))
    (hπL : ∀ v, (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight :
          L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom).toAddSubgroup =
      H₁.L.toAddSubgroup.map (π v))
    (hπt : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)) (π (v + 1) x) = π v x)
    (r' : ℕ) (H₂ : Deformation.HondaSystem (p : 𝓞) (Fin r' → 𝓞))
    (L' : ℕ → Type u) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra 𝓞 (L' v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L' v)] [∀ v, Module.Free 𝓞 (L' v)] [∀ v, Module.Finite 𝓞 (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[𝓞] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank 𝓞 (L' v) = p ^ (v * r'))
    (hkerL' : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L' (v + 1)) (p ^ v))
    (hunipL' : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L' v))))
    (π' : ∀ v, (Fin r' → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)))
    (hπ's : ∀ v, Function.Surjective (π' v))
    (hπ'k : ∀ v x, π' v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπ'F : ∀ v x, π' v (H₂.F x) =
      Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)) (π' v x))
    (hπ'V : ∀ v x, π' v (H₂.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)) (π' v x))
    (hπ'L : ∀ v, (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight :
          L' v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L' v)).toRingHom).toAddSubgroup =
      H₂.L.toAddSubgroup.map (π' v))
    (hπ't : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t' v)) (π' (v + 1) x) = π' v x)
    (φ : (Fin r' → 𝓞) →ₗ[𝓞] (Fin r → 𝓞))
    (hφF : φ ∘ₗ H₂.F = H₁.F ∘ₗ φ) (hφV : φ ∘ₗ H₂.V = H₁.V ∘ₗ φ)
    (hφL : Submodule.map φ H₂.L ≤ H₁.L) :
    ∃ f : ∀ v, L' v →ₐc[𝓞] L v,
      (∀ v, (f v).comp (t' v) = (t v).comp (f (v + 1))) ∧
      ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (f v)) (π' v x) = π v (φ x) := by sorry
