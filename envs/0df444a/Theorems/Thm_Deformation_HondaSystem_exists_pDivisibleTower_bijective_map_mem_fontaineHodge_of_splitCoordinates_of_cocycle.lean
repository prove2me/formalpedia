-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
-- name    : Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/f87f491f-b73c-5741-9d5d-2ca011a6d564
-- title:
--   Fontaine's lifting theorem from split coordinates and a cocycle
-- statement:
--   Let $\mathcal{O}$ be a commutative ring in which $p$ (a prime) is a non-zero-divisor, equipped with an $\mathcal{O}$-algebra structure on $\mathbb{Z}/p$ whose structure map has kernel $(p)$, and assume $\mathcal{O}$ is $(p)$-adically complete. Fix $r$ and a Honda system $H_1$ for the element $p$ on $\mathcal{O}^r$, that is, $\mathcal{O}$-linear $F,V$ with $FV=VF=p$ together with a submodule $L$ satisfying the four Honda conditions. Let $(G_v)_v$ be commutative cocommutative finite-dimensional Hopf algebras over $\mathbb{Z}/p$ with surjective bialgebra transitions $s_v\colon G_{v+1}\to G_v$, $\dim G_v=p^{vr}$, $\ker s_v$ the image of the augmentation ideal under the $p^v$-fold convolution power of the identity, and each Cartier dual $\operatorname{CartierDual}(\mathbb{Z}/p,G_v)$ a local ring. Let $\pi_v\colon \mathcal{O}^r\to \mathrm{DieudonneModule}(\mathbb{Z}/p,p,G_v)$ be surjective additive maps with $\pi_v x=0$ exactly for $x\in p^v\mathcal{O}^r$, intertwining $F$ and $V$ with the Dieudonné Frobenius and Verschiebung and compatible with the transitions via $\mathrm{DieudonneModule.map}$. Let $\mathcal{S}$ be a system of split coordinates for these data, assumed `Lawful`, and $\Phi$ a commutative $\mathcal{S}.d$-dimensional formal group law over $\mathcal{O}$ reducing modulo $p$ to $\mathcal{S}.\Phi_0$. Let $c_2(v)\in(\mathcal{S}.\mathrm{Et}\,v\otimes_{\mathcal{O}}\mathcal{S}.\mathrm{Et}\,v)^{\mathcal{S}.d}$ satisfy the hypothesis block `hCOC`: compatibility with $\mathcal{S}.\mathrm{st}_v\otimes\mathcal{S}.\mathrm{st}_v$, membership in the ideal $(p)$, vanishing when either tensor factor is replaced by the counit under lifts along any pair of $\mathcal{O}$-algebra maps into a $p$-torsion-free $(p)$-adically complete $\mathcal{O}$-algebra, symmetry under interchange of the two algebra maps, and the $2$-cocycle identity for $\Phi$ evaluated adically; and let `hLOGA` assert that for all such target algebras the sum of the two Witt series $\mathrm{wSeries}$ built from $\mathcal{S}.a$ (evaluated at radical arguments composed with $\Phi$) and from $\mathcal{S}.\hat c$ is additive in the pair of algebra maps. Then there exist $\mathcal{O}$-algebras $L_v$ that are commutative cocommutative Hopf algebras, free and finite as $\mathcal{O}$-modules, with surjective bialgebra transitions $t_v\colon L_{v+1}\to L_v$ such that $\operatorname{rank}_{\mathcal{O}}L_v=p^{vr}$ and $\ker t_v$ is the $p^v$-torsion ideal of $L_{v+1}$, and bijective $\mathbb{Z}/p$-bialgebra maps $e_v\colon G_v\to (\mathbb{Z}/p)\otimes_{\mathcal{O}}L_v$ with $e_v\circ s_v=(\mathrm{id}\otimes t_v)\circ e_{v+1}$, such that for every $x\in H_1.L$ the image of $\pi_v x$ under $\mathrm{DieudonneModule.map}$ of $e_v$ lies in the Fontaine–Hodge submodule attached to the ring map $L_v\to(\mathbb{Z}/p)\otimes_{\mathcal{O}}L_v$.
--
--   This is the construction of the levels in Fontaine's lifting theorem along the connected–étale (split coordinates) route: from a cocycle twisting the lifted formal group law it produces the $p$-divisible tower over $\mathcal{O}$ together with the identification of its special fibre and the Fontaine–Hodge condition on the image of the Honda submodule. It is used by [`Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod`](thm.html#Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod), where the split coordinates and the cocycle are supplied from a unipotent $p$-divisible tower over $\mathbb{Z}/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.lean

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

theorem Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
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

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (h𝒮 : 𝒮.Lawful)

    (Φ : MvFormalGroup 𝒮.d 𝓞) [Φ.IsComm] (hΦ : Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀)

    (c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
    (hCOC :
      (∀ v i, Algebra.TensorProduct.map (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v)
          (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v) (c₂ (v + 1) i) = c₂ v i) ∧
      (∀ v i, c₂ v i ∈ Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)}) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f : 𝒮.Et v →ₐ[𝓞] g) (j : Fin 𝒮.d),
          Algebra.TensorProduct.lift f ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (𝒮.Et v))) (fun _ _ => Commute.all _ _) (c₂ v j) = 0 ∧
          Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (𝒮.Et v))) f (fun _ _ => Commute.all _ _) (c₂ v j) = 0) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (j : Fin 𝒮.d),
          Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j) = Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ v j)) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' f'' : 𝒮.Et v →ₐ[𝓞] g),
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) f'' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)) =
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i))))

    (hLOGA :
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (x x' : Fin 𝒮.d → g),
          (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, x' j ∈ (Ideal.span {(p : g)}).radical) → ∀ i : Fin 𝒮.d,
          Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)})
              (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x) ((fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x') ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) (Φ.toPowerSeries i)) (𝒮.a i n)) +
            Deformation.PLoc.wSeries p (fun k => ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (𝒮.ĉ i k v)) =
          (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f (𝒮.ĉ i k v))) +
            (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x' (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f' (𝒮.ĉ i k v))))) :
    ∃ (L : ℕ → Type u) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra 𝓞 (L v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L v)) (_ : ∀ v, Module.Free 𝓞 (L v))
      (_ : ∀ v, Module.Finite 𝓞 (L v)) (t : ∀ v, L (v + 1) →ₐc[𝓞] L v),
      (∀ v, Function.Surjective (t v)) ∧ (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
    ∃ e : ∀ v, G v →ₐc[ZMod p] TensorProduct 𝓞 (ZMod p) (L v),
      (∀ v, Function.Bijective (e v)) ∧
      (∀ v, (e v).comp (s v) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)).comp (e (v + 1))) ∧
      (∀ v, ∀ x ∈ H₁.L, Deformation.DieudonneModule.map (ZMod p) p (e v) (π v x) ∈
        Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom) := by sorry
