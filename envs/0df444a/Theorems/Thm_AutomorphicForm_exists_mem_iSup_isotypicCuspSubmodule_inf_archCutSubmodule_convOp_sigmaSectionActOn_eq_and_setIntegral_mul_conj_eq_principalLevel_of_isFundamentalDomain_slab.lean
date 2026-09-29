-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9de0ab8f-59d0-5eb4-a975-dd9248d4dacd
-- title:
--   Galois twist matched by a cut cuspidal vector
-- statement:
--   Let $L/K$ be an extension of number fields, $D$ a Galois descent datum for the adeles of $L$ over $K$ (a continuous action $\mathrm{Aut}_K(L)\to\mathrm{Aut}(\mathbb{A}_L)$ compatible with $L\to\mathbb{A}_L$), and $\sigma$ a $K$-automorphism of $L$; write $\sigma_{\mathbb{A}}$ for the induced map on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\sigma^{*}u=u\circ\sigma_{\mathbb{A}}$. Let $0<\alpha<\beta$ and let $\Phi\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ be contained in the slab $\{g:\|\det g\|\in[\alpha,\beta]\}$ and be a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on the slab with the restricted adelic Haar measure. Let $\xi$ be a character of the full idele unit group with $\xi\circ\sigma_{\mathbb{A}}=\xi$, let $S_L$ be a finite set of finite places of $L$ whose membership depends only on the place of $K$ below, $N$ an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$, and $\mathrm{tys}_L$ a family assigning to each infinite place $w$ of $L$ finitely many representations of the determinant-one row-isometry group at $w$. Take the pins with carrier $\Phi$, adelic Haar measure, central subgroup the full idele units, level family $M\mapsto U(M)\cap\mathrm{GL}_2(\mathbb{A}_L)_{\mathrm{fin}}$ for the principal congruence subgroups, the standard Hecke generators, and the adelic box as box measure. For a Hecke eigensystem $\pi$ (level ideal, nonzero, with coefficients $a,b$) write $W_\pi$ for the $\mathbb{C}$-span of the functions that are isotypic cusp forms at these pins for $(\xi,N,S_L,\pi)$ — smooth cuspidal with central character $\xi$, continuous, right $U(N)\cap\mathrm{GL}_2(\mathbb{A}_L)_{\mathrm{fin}}$-invariant, Hecke eigenfunctions with eigenvalue $\pi.a(v)$ and central eigenvalue $\pi.b(v)$ at $v\notin S_L$ — intersected with the archimedean cut submodule of $\mathrm{tys}_L$, the intersection over infinite places $w$ of the sum of the type submodules attached to the representations at $w$. Let $\Psi$ be a cuspidal class for $(\xi,N,S_L)$, that is $\Psi.\mathrm{level}=N$, $\Psi.a(v)=\Psi.b(v)=0$ for $v\in S_L$, and $W_\Psi$-span nonzero, and let $u\in W_\Psi$. Then there is $u_1$ in the supremum of the $W_\pi$ over the cuspidal classes $\pi$ for $(\xi,N,S_L)$ such that, first, for every continuous compactly supported $f:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ that is bi-invariant under $U(N)\cap\mathrm{GL}_2(\mathbb{A}_L)_{\mathrm{fin}}$ and satisfies that $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule and $f$ in the archimedean dual cut submodule of $\mathrm{tys}_L$, the right convolutions agree: $g\mapsto\int (\sigma^{*}u)(gx)f(x)\,dx$ equals $g\mapsto\int u_1(gx)f(x)\,dx$; and second, for every cuspidal class $\pi$ and every $b\in W_\pi$, $\int_\Phi(\sigma^{*}u)(x)\overline{b(x)}\,dx=\int_\Phi u_1(x)\overline{b(x)}\,dx$.
--
--   This is the step that replaces the $\sigma$-twist of a cut cuspidal vector by an honest vector of the cut cuspidal spectrum at level $N$: the replacement is indistinguishable from the twist both by all admissible convolution operators and by all pairings against the cut isotypic blocks over the fundamental domain. It is used in the comparison of the twisted and untwisted convolution sums over an orthonormal family, in the base-change analysis of automorphic forms on $\mathrm{GL}_2$ over $L$ relative to $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξ ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξ ⟨z, Subgroup.mem_top z⟩)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : Ψ ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : u ∈ isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL Ψ ⊓ archCutSubmodule L tysL) :
    ∃ u₁ ∈ ⨆ (π : HeckeEigensystem L ℂ) (_ : π ∈ cuspClasses L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL),
        isotypicCuspSubmodule L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL π ⊓ archCutSubmodule L tysL,
      (∀ (f : AdelicGL2 (𝓞 L) L → ℂ), Continuous f → HasCompactSupport f →
          IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f →
          IsArchBiFinite L tysL f →
        convOp L f (sigmaSectionActOn K L D σ u) = convOp L f u₁) ∧
      ∀ π ∈ cuspClasses L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL,
      ∀ b ∈ isotypicCuspSubmodule L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL π ⊓ archCutSubmodule L tysL,
        ∫ x in Φ, sigmaSectionActOn K L D σ u x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
          ∫ x in Φ, u₁ x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
