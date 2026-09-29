-- Prove2me | Theorems.Thm_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d17b4669-4703-5da4-b6aa-d3202407f87d
-- title:
--   Cuspidal class contribution equals its twisted cut trace
-- statement:
--   Let $L/K$ be an extension of number fields, $\sigma$ a $K$-automorphism of $L$, and $D$ a datum consisting of an action of the $K$-automorphisms of $L$ on the adele ring $\mathbb A_L$ by continuous ring automorphisms compatible with the map on principal adeles; write $\sigma_{\mathbb A}$ for the resulting map on $G=\mathrm{GL}_2(\mathbb A_L)$. Fix reals $0<\alpha<\beta$ and put $\mathcal S=\{g\in G:\ \|\det g\|\in[\alpha,\beta]\}$, the norm being the module of the distinguished Haar character. Let $\Phi_L$ and $\Phi_0$ be subsets of $\mathcal S$, each a fundamental domain for the image of $\mathrm{GL}_2(L)$ in $G$ with respect to adelic Haar measure restricted to $\mathcal S$. Let $\xi_L$ be a homomorphism from the full unit group of $\mathbb A_L$ to $\mathbb C^\times$, $S_L$ a finite set of finite places of $L$ that is a union of fibres over places of $K$, $N$ an ideal of $\mathcal O_L$ all of whose prime divisors lie in $S_L$, and $\mathrm{tys}_L$ an archimedean type family (finitely many representations of the row-isometry subgroup at each infinite place). The carrier data are those produced from $\Phi_L$: Borel structure and Haar measure on $G$, central subgroup the whole idele unit group, level subgroups $M\mapsto \mathrm{levelOne}(M)\cap G_{\mathrm{fin}}$, Hecke generators $\mathrm{heckeGen}(w)$, and the adelic box for the conditioned additive measure. For a Hecke eigensystem $\pi$ let $V_\pi$ be the span of the isotypic cusp forms of $\pi$ with character $\xi_L$, level $N$ and exceptional set $S_L$, and $W_\pi=V_\pi\cap\mathrm{Cut}(\mathrm{tys}_L)$. Given a type $\iota$, functions $b_i:G\to\mathbb C$ and classes $\mathrm{cls}(i)$ with each $\mathrm{cls}(i)$ a cuspidal class (level $N$, vanishing eigenvalues on $S_L$, $V_{\mathrm{cls}(i)}\neq 0$) and $b_i\in W_{\mathrm{cls}(i)}$, assume $\int_{\Phi_L}b_i\overline{b_i}=1$, $\int_{\Phi_L}b_i\overline{b_j}=0$ for $i\neq j$, and that for every cuspidal class $\pi$ the set $\{i:\mathrm{cls}(i)=\pi\}$ is finite with $\mathbb C$-span of the corresponding $b_i$ equal to $W_\pi$. Let $\varphi$ be continuous with compact support, invariant on both sides under $\mathrm{levelOne}(N)\cap G_{\mathrm{fin}}$, and archimedeanly bi-finite for $\mathrm{tys}_L$ (namely $g\mapsto\varphi(g^{-1})$ lies in the archimedean cut submodule and $\varphi$ in the dual cut submodule). Then for every cuspidal class $\Psi$ the finite sum over $\{i:\mathrm{cls}(i)=\Psi\}$ of $\int_{\Phi_0}\bigl(\int_G b_i(\sigma_{\mathbb A}(xy))\varphi(y)\,dy\bigr)\overline{b_i(x)}\,dx$ equals the $\sigma$-twisted cut trace of $\varphi$ on $W_\Psi$, that is, the trace of $u\mapsto\bigl(g\mapsto\int_G u(\sigma_{\mathbb A}(gy))\varphi(y)\,dy\bigr)$ on $W_\Psi$ if this operator preserves $W_\Psi$, and $0$ otherwise.
--
--   This is the class-by-class identification of the cuspidal spectral term of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L$: the contribution of a single cuspidal class, computed as a sum of diagonal matrix coefficients against an orthonormal family on a fundamental domain of the determinant slab, is its twisted cut trace. It feeds the later assembly of the spectral side, where the contributions of all classes are summed and compared with the geometric side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (hφt : IsArchBiFinite L tysL φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : Ψ ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL) :
    ∑ᶠ i : {i // cls i = Ψ},
        ∫ x in Φ₀, twistedConvOp K L D σ φ (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      twistedCutTrace K L D σ
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc := by sorry
