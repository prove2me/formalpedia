-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates
-- name    : Deformation.HondaSystem.exists_mem_fontaineFunctor_of_coords_of_splitCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/b2fd5799-8151-5b1f-9f03-76d445463ca6
-- title:
--   Existence in Fontaine's functor with prescribed split coordinates
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal{O}$, $\mathcal{O}$ carries an algebra structure on $\mathbb{Z}/p$ whose structure map has kernel $(p)$, and $\mathcal{O}$ is complete for the $(p)$-adic filtration. Fix $r$ and a Honda system $H_1$ for the element $p$ on $\mathcal{O}^r$, that is, maps $F,V$ with $FV=VF=p\cdot\mathrm{id}$ together with a submodule $L = H_1.L$ satisfying the conditions `sh1_le`, `sh1_ge`, `sh2'`, `sh3`. Let $G$ be a tower of finite cocommutative $\mathbb{Z}/p$-Hopf algebras with surjective bialgebra transition maps $s_v : G(v+1) \to G(v)$, $\dim_{\mathbb{Z}/p} G(v) = p^{vr}$, $\ker(s_v)$ the $p^v$-torsion ideal of $G(v+1)$, and each Cartier dual $\mathrm{CartierDual}(\mathbb{Z}/p, G(v))$ a local ring; let $\pi_v : \mathcal{O}^r \to M(G(v))$ be surjective additive maps into the Dieudonné modules with $\pi_v x = 0$ exactly for $x \in p^v\mathcal{O}^r$, carrying $F$ and $V$ to the Frobenius and Verschiebung of $M(G(v))$ and compatible with the maps induced by $s_v$. Let $\mathcal{S}$ be a system of split coordinates [`Deformation.HondaSystem.SplitCoordinates`](def/Deformation_SplitCoordinates.html#L22) for these data, assumed `Lawful` and in `NormalForm`, with connected and étale factors $\mathcal{S}.Gc$, $\mathcal{S}.Ge$, splitting $\Theta_v : G(v) \to \mathcal{S}.Gc\,v \otimes_{\mathbb{Z}/p} \mathcal{S}.Ge\,v$, coordinate surjections $\kappa_v$ on $\mathcal{S}.d$ variables, étale lifts $\mathcal{S}.Et\,v$ with comparison maps $\theta^e_v$, basis $\mathcal{S}.\alpha$ of $L$, and series $\mathcal{S}.a$, $\mathcal{S}.\hat c$. Let $g$ be a commutative $\mathcal{O}$-algebra in which $p$ is a non-zero-divisor and which is $(p)$-adically complete, let $v_1$ be a level, $y_1 : \mathcal{S}.Et\,v_1 \to g$ an $\mathcal{O}$-algebra map, and $x : \mathrm{Fin}\,\mathcal{S}.d \to g$ a tuple with every $x_j$ in the radical of $(p)$, and assume there is a $\mathbb{Z}/p$-algebra map $\mathcal{S}.Gc\,v_1 \to (\mathbb{Z}/p) \otimes_{\mathcal{O}} g$ sending $\kappa_{v_1}(X_i)$ to $1 \otimes x_i$. Then there is a pair $z$ consisting of an $\mathcal{O}$-linear map $z_1 : L \to g[1/p]$ and an additive map $z_2 : \mathcal{O}^r \to \mathrm{UnipotentWittCovector}\,p\,((\mathbb{Z}/p) \otimes_{\mathcal{O}} g)$ such that: $z$ lies in [`Deformation.HondaSystem.fontaineFunctor`](def/Dieudonne_FontaineFunctor.html#L479) for $H_1$ along the right inclusion $g \to (\mathbb{Z}/p) \otimes_{\mathcal{O}} g$; $z_2$ is killed by $p^{v_0}$ for some $v_0$; there are $\mathbb{Z}/p$-algebra maps $f$ on $\mathcal{S}.Gc\,v_1$ and $e$ on $\mathcal{S}.Ge\,v_1$ with values in $(\mathbb{Z}/p) \otimes_{\mathcal{O}} g$ such that $z_2$ is the composite of $\pi_{v_1}$ with the evaluation of $\Theta_{v_1}$ followed by the map induced by $f$ and $e$ on the tensor product, with $e \circ \theta^e_{v_1} = \mathrm{id} \otimes y_1$ and $f(\kappa_{v_1}(X_i)) = 1 \otimes x_i$; and, for every level $v$ and every triple $(f, e, y)$ with $y : \mathcal{S}.Et\,v \to g$ an $\mathcal{O}$-algebra map for which $z_2$ factors in the same way through $\pi_v$ and $e \circ \theta^e_v = \mathrm{id} \otimes y$, one has $f(\kappa_v(X_i)) = 1 \otimes x_i$ for all $i$ and $$z_1(\mathcal{S}.\alpha_i) = w\text{-series}\big(n \mapsto \mathrm{adicEval}_{(p)}\,x\,(\mathcal{S}.a\,i\,n)\big) + w\text{-series}\big(k \mapsto y(\mathcal{S}.\hat c\,i\,k\,v)\big)$$ in $g[1/p]$.
--
--   This is the existence half of Fontaine's lemma on points of the functor attached to a Honda system (Groupes $p$-divisibles sur les corps locaux, Ch. IV), in the form allowing a non-trivial étale part: given a topologically nilpotent coordinate tuple that is already realised at level $v_1$ and an étale point there, it produces a member of the functor whose connected coordinates are the given tuple and whose linear component on $L$ is given by the explicit $w$-series formula, the last clause recording that these data determine the coordinates at every admissible level. It feeds the construction of $p$-divisible towers lifting a given tower over $\mathbb{Z}/p$ with prescribed Hodge datum, in [`Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod`](thm.html#Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Deformation_SplitCoordinates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open MvPowerSeries

universe u v w

theorem Deformation.HondaSystem.exists_mem_fontaineFunctor_of_coords_of_splitCoordinates
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful) (hNF : 𝒮.NormalForm)
    (g : Type u) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    [IsAdicComplete (Ideal.span {(p : g)}) g]
    (v₁ : ℕ) (y₁ : 𝒮.Et v₁ →ₐ[𝓞] g)
    (x : Fin 𝒮.d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)

    (hx₁ : ∃ f : 𝒮.Gc v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g, ∀ i, f (𝒮.κ v₁ (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i) :
    ∃ z : (H₁.L →ₗ[𝓞] Localization.Away (p : g)) ×
      ((Fin r → 𝓞) →+ Deformation.UnipotentWittCovector p (TensorProduct 𝓞 (ZMod p) g)),
      z ∈ Deformation.HondaSystem.fontaineFunctor p H₁ (ZMod p)
      (Algebra.TensorProduct.includeRight : g →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g).toRingHom ∧
      (∃ v₀ : ℕ, ∀ m : Fin r → 𝓞, z.2 ((p : 𝓞) ^ v₀ • m) = 0) ∧

      (∃ (f : 𝒮.Gc v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (e : 𝒮.Ge v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
        z.2 = (Deformation.DieudonneModule.eval (ZMod p) p
                ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp
                  (𝒮.Θ v₁ : G v₁ →ₐ[ZMod p] 𝒮.Gc v₁ ⊗[ZMod p] 𝒮.Ge v₁))).comp (π v₁) ∧
        e.comp (𝒮.θe v₁ : ZMod p ⊗[𝓞] 𝒮.Et v₁ →ₐ[ZMod p] 𝒮.Ge v₁) =
          Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y₁ ∧
        (∀ i, f (𝒮.κ v₁ (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i)) ∧

      (∀ (v : ℕ) (f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
          (e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (y : 𝒮.Et v →ₐ[𝓞] g),

          z.2 = (Deformation.DieudonneModule.eval (ZMod p) p
                  ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp
                    (𝒮.Θ v : G v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v))).comp (π v) →

          e.comp (𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐ[ZMod p] 𝒮.Ge v) =
            Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y →
          (∀ i, f (𝒮.κ v (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i) ∧
          (∀ i, z.1 (𝒮.α i) =
            Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
            Deformation.PLoc.wSeries p (fun k => y (𝒮.ĉ i k v)))) := by sorry
