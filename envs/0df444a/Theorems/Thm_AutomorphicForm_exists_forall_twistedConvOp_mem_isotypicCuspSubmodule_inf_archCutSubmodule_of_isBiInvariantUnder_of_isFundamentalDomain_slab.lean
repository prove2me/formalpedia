-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isBiInvariantUnder_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isBiInvariantUnder_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/90460615-beb1-59f3-b605-2f96deee0fec
-- title:
--   Galois-twisted convolution carries isotypic cusp spaces to a single eigensystem
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idele Galois descent datum for $L/K$ (a homomorphism from the $K$-automorphisms of $L$ to the continuous ring automorphisms of $\mathbb{A}_L$, compatible with the map on principal adeles), and let $\sigma$ be a $K$-automorphism of $L$. Let $0 < \alpha < \beta$ be real, and let $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ be contained in the determinant slab $\{g : \|\det g\|_{\mathbb{A}_L} \in [\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character, and be a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on the Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to that slab. Let $\xi_L : \mathbb{A}_L^{\times} \to \mathbb{C}^{\times}$ (formally, a character of the top subgroup) satisfy $\xi_L(\sigma_{\mathbb{A}} z) = \xi_L(z)$ for all ideles $z$, where $\sigma_{\mathbb{A}} = D.\mathrm{act}\,\sigma$. Let $S_L$ be a finite set of finite places of $L$ whose membership depends only on the place of $K$ below, let $N$ be an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$, let $\mathrm{tys}_L$ be a family of archimedean types (finitely many representations of the row-isometry subgroup at each infinite place), and let $\Psi$ be a Hecke eigensystem over $\mathbb{C}$ with $\Psi.\mathrm{level} = N$. Throughout, the carrier data are the production pins `productionPinsOf` built from $\Phi_L$, the level subgroups $\mathrm{levelOne}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators `heckeGen`, and the adelic box (so that the central subgroup is all of $\mathbb{A}_L^{\times}$). Then there is a Hecke eigensystem $\Psi'$ of level $N$ with $\Psi'.a(w) = \Psi'.b(w) = 0$ for every $w \in S_L$ such that, for every continuous compactly supported $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ which is bi-invariant under $\mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$ and satisfies `IsArchBiFinite` for $\mathrm{tys}_L$ (that is, $g \mapsto \varphi(g^{-1})$ lies in the archimedean cut submodule of $\mathrm{tys}_L$ and $\varphi$ in the dual cut submodule), and for every $u$ in the intersection of the $\Psi$-isotypic cusp submodule (the $\mathbb{C}$-span of the functions that are continuous, right invariant under $\mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, smooth cuspidal with central character $\xi_L$ for the given pins, Hecke eigenfunctions with eigenvalue $\Psi.a(w)$ and central eigenvalue $\Psi.b(w)$ at each $w \notin S_L$) with the archimedean cut submodule of $\mathrm{tys}_L$, the twisted convolution $g \mapsto \int u(\sigma_{\mathbb{A}}(gx))\,\varphi(x)\,dx$ lies in the intersection of the $\Psi'$-isotypic cusp submodule with the same archimedean cut submodule.
--
--   This is the transport of automorphic data by a Galois twist: convolution with a suitable test function composed with the $\sigma$-action on $\mathrm{GL}_2(\mathbb{A}_L)$ permutes the isotypic blocks of cusp forms, sending the block of $\Psi$ into the block of a single eigensystem $\Psi'$ of the same level, normalised to vanish at the places of $S_L$. It is the block-stability input to the computation of the twisted trace of such an operator against an orthonormal family on the fundamental domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isBiInvariantUnder_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isBiInvariantUnder_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Ψ : HeckeEigensystem L ℂ) (hΨN : Ψ.level = N) :
    ∃ Ψ' : HeckeEigensystem L ℂ, Ψ'.level = N ∧ (∀ w ∈ SL, Ψ'.a w = 0 ∧ Ψ'.b w = 0) ∧
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ), Continuous φ → HasCompactSupport φ →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ ⊓ archCutSubmodule L tysL,
        twistedConvOp K L D σ φ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ' ⊓ archCutSubmodule L tysL := by sorry
