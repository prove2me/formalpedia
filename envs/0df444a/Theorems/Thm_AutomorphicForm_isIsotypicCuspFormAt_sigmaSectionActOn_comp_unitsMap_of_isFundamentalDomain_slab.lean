-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/c1c1d82f-25d4-5be2-b2e2-5ce8e5adf183
-- title:
--   Galois twist of isotypic cusp forms, with twisted central character
-- statement:
--   Let $L/K$ be an extension of number fields, let $\sigma$ be a $K$-automorphism of $L$, and let $D$ be an idele Galois descent datum for $\mathcal O_L$ over $K\subseteq L$, i.e. a monoid homomorphism $\mathrm{Aut}_K(L)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb A_L)$ whose values are continuous and agree with the given action on principal adeles. Fix reals $\alpha,\beta$ and a set $\Phi_L\subseteq\mathrm{GL}_2(\mathbb A_L)$ contained in the slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), and which is a fundamental domain for the range of `globalPoints` (the image of $\mathrm{GL}_2(L)$) acting on that slab with respect to the restriction of `adelicGLHaar` to the slab. Let $\xi_L$ be a homomorphism from the whole group $\mathbb A_L^\times$ (as the subgroup $\top$) to $\mathbb C^\times$, let $S_L$ be a finite set of finite places of $L$ whose membership depends only on the place of $K$ below, let $N$ be an ideal of $\mathcal O_L$, and let $\Psi$ be a Hecke eigensystem over $\mathbb C$ (a nonzero level ideal together with families $a,b$ indexed by the finite places). Write `pins` for `productionPinsOf` built from $\Phi_L$, the level subgroups $M\mapsto$ `levelOne` $M$ intersected with `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` $w$, and the adelic box. Assume $u:\mathrm{GL}_2(\mathbb A_L)\to\mathbb C$ satisfies `IsIsotypicCuspFormAt` for these pins, $\xi_L$, $N$, $S_L$, $\Psi$: it satisfies `IsSmoothCuspAutomorphicFnAt`, it is continuous, it is right invariant under `levelOne` $N$ intersected with `finiteAdelicGL2Subgroup`, and for every $v\notin S_L$ it is a Hecke coset eigenfunction at `heckeGen` $v$ with eigenvalue $\Psi.a\,v$ and satisfies the central translation relation by $\det(\mathtt{heckeGen}\ v)$ with eigenvalue `Ψ.toRawCentral.b v`. Then the twist `sigmaSectionActOn K L D σ u`, namely $u\circ\sigma_{\mathbb A}$ for the action $\sigma_{\mathbb A}$ of $\sigma$ on $\mathrm{GL}_2(\mathbb A_L)$ induced by $D$, satisfies `IsIsotypicCuspFormAt` for the same pins and the same $S_L$, for the character $\xi_L\circ(\text{units of }D.\mathrm{act}\,\sigma)$, for the level ideal obtained by pulling $N$ back along the ring endomorphism of $\mathcal O_L$ given by $\sigma$, and for the Hecke eigensystem with the same level as $\Psi$, with $a$-values $w\mapsto\Psi.a(\sigma\cdot w)$ and with $b$-values $w\mapsto \mathrm{N}(w)\cdot\xi_L\bigl(\sigma_{\mathbb A}(\det(\mathtt{heckeGen}\ w))\bigr)$, where $\mathrm{N}(w)$ is `HeckeEigensystem.cNorm w`, the absolute norm of $w$ viewed in $\mathbb C$.
--
--   This is the statement that the Galois action $\pi\mapsto\pi^\sigma$ permutes the cuspidal spectrum, formulated for isotypic cusp forms read on a fixed fundamental domain in a determinant slab: no $\sigma$-invariance of the central character is assumed, the twisted form having central character $\xi_L\circ\sigma_{\mathbb A}$, transported level $\sigma^{-1}N$ and transported Hecke data. It is used in the construction of twisted convolution operators on isotypic cusp spaces of an arbitrary central character, and in the integrability and summability estimates for the associated kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped NumberField.PlaceTransport

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (Ψ : HeckeEigensystem L ℂ)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ u) :
    IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L))
      (ξL.comp (Subgroup.topEquiv.symm.toMonoidHom.comp
        ((Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
            AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)).comp Subgroup.topEquiv.toMonoidHom)))
      (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) SL
      ⟨Ψ.level, Ψ.level_ne_bot, fun w => Ψ.a (σ • w), fun w =>
        HeckeEigensystem.cNorm w *
          ((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
              AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)
            (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)⟩
      (sigmaSectionActOn K L D σ u) := by sorry
