-- Prove2me | Theorems.Thm_Deformation_HondaSystem_existsUnique_coords_of_mem_fontaineFunctor_of_splitCoordinates
-- name    : Deformation.HondaSystem.existsUnique_coords_of_mem_fontaineFunctor_of_splitCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5762f3ef-d215-57ee-acbd-9a0c7433bfcf
-- title:
--   Unique split coordinates of a continuous point of Fontaine's functor
-- statement:
--   Let $\mathcal{O}$ be a commutative ring in which the prime $p$ is a non-zero-divisor, equipped with an algebra structure over $\mathbb{Z}/p$ whose structure map has kernel exactly $(p)$, and complete for the $(p)$-adic topology. Fix $r$ and a Honda system $H_1$ for the element $p$ on $\mathcal{O}^r$, i.e. endomorphisms $F,V$ with $FV=VF=p\cdot\mathrm{id}$ together with a submodule $L=H_1.L$ satisfying Fontaine's four conditions. Let $G_v$ ($v\in\mathbb{N}$) be commutative rings carrying cocommutative Hopf algebra structures over $\mathbb{Z}/p$, finite-dimensional, with surjective bialgebra transition maps $s_v\colon G_{v+1}\to G_v$, $\dim G_v=p^{vr}$, $\ker(s_v)$ the $p^v$-torsion ideal (the image of the augmentation ideal under multiplication by $p^v$), and each Cartier dual $\operatorname{CartierDual}(\mathbb{Z}/p,G_v)$ a local ring. Let $\pi_v\colon \mathcal{O}^r\to \mathrm{DieudonneModule}(\mathbb{Z}/p,p,G_v)$ be surjective additive maps whose vanishing locus is $p^v\mathcal{O}^r$, carrying $H_1.F$, $H_1.V$ to Frobenius and Verschiebung and compatible with the $s_v$. Let $\mathcal{S}$ be a system of split coordinates for these data — with connected and étale parts $\mathcal{S}.Gc_v$, $\mathcal{S}.Ge_v$, the isomorphism $\Theta_v\colon G_v\to \mathcal{S}.Gc_v\otimes_{\mathbb{Z}/p}\mathcal{S}.Ge_v$, coordinates $\kappa_v$ on $\mathcal{S}.Gc_v$ for the formal group law $\Phi_0$ in $d=\mathcal{S}.d$ variables, the $\mathcal{O}$-Hopf algebras $\mathcal{S}.Et_v$ with $\theta^e_v\colon \mathbb{Z}/p\otimes_{\mathcal{O}}\mathcal{S}.Et_v\to \mathcal{S}.Ge_v$, a basis $\alpha$ of $L$, and the data $a_{i,n}$, $\hat c_{i,k,v}$ — assumed `Lawful` and in `NormalForm` (the reduction mod $p$ of the linear part of $(a_{i,0})_i$ is the identity matrix, and the entries of the linear part of $(a_{i,1})_i$ on and below the diagonal lie in $(p)$). Let $g$ be an $\mathcal{O}$-algebra in which $p$ is a non-zero-divisor and which is $(p)$-adically complete, and let $z=(\xi,\eta)$ with $\xi\colon L\to \mathcal{O}$-linearly into $\mathrm{Localization.Away}(p)$ of $g$ and $\eta\colon \mathcal{O}^r\to \mathrm{UnipotentWittCovector}\,p\,(\mathbb{Z}/p\otimes_{\mathcal{O}}g)$ an element of `fontaineFunctor` for the ring map $g\to \mathbb{Z}/p\otimes_{\mathcal{O}}g$ (so $\eta$ intertwines $F,V$ with Frobenius and Verschiebung, and each $\eta(l)$, $l\in L$, comes from a covector $Z$ over $g$ with $\xi(l)\equiv wUp(Z)$ modulo `PLoc.pSub`), subject to the continuity hypothesis that $\eta$ kills $p^{v_0}\mathcal{O}^r$ for some $v_0$. Then there is a unique $x\colon \mathrm{Fin}\,d\to g$ with all $x_j$ in the radical of $(p)$ such that for every level $v$, all $\mathbb{Z}/p$-algebra maps $f\colon \mathcal{S}.Gc_v\to \mathbb{Z}/p\otimes_{\mathcal{O}}g$ and $e\colon \mathcal{S}.Ge_v\to \mathbb{Z}/p\otimes_{\mathcal{O}}g$ and every $\mathcal{O}$-algebra map $y\colon \mathcal{S}.Et_v\to g$: if $\eta$ equals $\pi_v$ followed by the Dieudonné-module evaluation at $\Theta_v$ composed with the map induced by $f$ and $e$, and if $e\circ\theta^e_v$ is the base change $\mathrm{id}\otimes y$, then $f(\kappa_v(X_i))=1\otimes x_i$ for all $i$ and $\xi(\alpha_i)=\mathrm{wSeries}_p\big(n\mapsto a_{i,n}(x)\big)+\mathrm{wSeries}_p\big(k\mapsto y(\hat c_{i,k,v})\big)$ for all $i$, where $a_{i,n}(x)$ denotes the $(p)$-adic evaluation of the power series $a_{i,n}$ at $x$ and $\mathrm{wSeries}$ is the $p$-adic limit of the partial sums $\sum_{n<N}p^{-n}c_n^{p^n}$ in $\mathrm{Localization.Away}(p)$.
--
--   This is Fontaine's uniqueness-and-characterisation lemma for points of the functor attached to a Honda system, in the form that allows a non-trivial étale part: a continuous point of the functor is determined by, and determines, the $d$-tuple of topologically nilpotent coordinates of its connected component, with the linear part of the point computed by the Artin–Hasse-type series in those coordinates plus the contribution of an étale lift. It feeds the construction of a $p$-divisible tower over $g$ lifting a given tower over $\mathbb{Z}/p$, in [`Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod`](thm.html#Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_existsUnique_coords_of_mem_fontaineFunctor_of_splitCoordinates.lean

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

theorem Deformation.HondaSystem.existsUnique_coords_of_mem_fontaineFunctor_of_splitCoordinates
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
    (z : (H₁.L →ₗ[𝓞] Localization.Away (p : g)) ×
      ((Fin r → 𝓞) →+ Deformation.UnipotentWittCovector p (TensorProduct 𝓞 (ZMod p) g)))
    (hz : z ∈ Deformation.HondaSystem.fontaineFunctor p H₁ (ZMod p)
      (Algebra.TensorProduct.includeRight : g →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g).toRingHom)
    (hzcont : ∃ v₀ : ℕ, ∀ m : Fin r → 𝓞, z.2 ((p : 𝓞) ^ v₀ • m) = 0) :
    ∃! x : Fin 𝒮.d → g, (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) ∧
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
