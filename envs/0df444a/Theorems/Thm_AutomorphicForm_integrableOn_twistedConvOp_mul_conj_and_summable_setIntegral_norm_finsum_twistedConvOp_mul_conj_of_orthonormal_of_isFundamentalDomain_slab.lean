-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/6e7b08f5-c352-53fd-85bb-bc4a947c7d69
-- title:
--   Class-by-class trace-norm summability of twisted convolution kernels
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idèle Galois descent datum for $L/K$ (a monoid homomorphism from $K$-automorphisms of $L$ to continuous ring automorphisms of $\mathbb{A}_L$ compatible with the action on $L$), and let $\sigma$ be a $K$-automorphism of $L$; write $\sigma_{\mathbb A}$ for the induced map on $G = \mathrm{GL}_2(\mathbb{A}_L)$ and $\mu$ for the Haar measure `adelicGLHaar` on $G$. Fix reals $0 < \alpha < \beta$ and let $\Sigma = \{g : \|\det g\| \in [\alpha,\beta]\}$, the idèle norm being the module of the adelic Haar measure. Let $\Phi_L$ and $\Phi_0$ be subsets of $\Sigma$, each a fundamental domain for the image of $\mathrm{GL}_2(L)$ in $G$ with respect to $\mu$ restricted to $\Sigma$. Let $\xi_L$ be a homomorphism from the full group of idèle units of $L$ to $\mathbb{C}^\times$, let $S_L$ be a finite set of finite places of $L$ that is a union of fibres over $K$ (two places lying under the same place of $K$ are simultaneously in or out of $S_L$), let $N$ be an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$, and let $\mathrm{tys}_L$ be an archimedean type family on $L$ (a finite list of representations of the row-isometry subgroup at each infinite place). Carrier data are taken to be `productionPinsOf L ΦL` with level subgroups $M \mapsto$ `levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L`, Hecke generators `heckeGen (𝓞 L) L w` and box `adelicBox L`. Let $\iota$ be a type, $b : \iota \to (G \to \mathbb{C})$ and $\mathrm{cls} : \iota \to$ `HeckeEigensystem L ℂ` be such that: each $\mathrm{cls}\,i$ is a cuspidal class for these data (level $N$, vanishing $a_v$ and $b_v$ for $v \in S_L$, nonzero isotypic cuspidal submodule), and each $b_i$ lies in the span of the isotypic cusp forms with Hecke eigenvalues $(\mathrm{cls}\,i).a$ and central eigenvalues $(\mathrm{cls}\,i).b$ outside $S_L$, intersected with the archimedean cut submodule `archCutSubmodule L tysL`; $\int_{\Phi_L} b_i \overline{b_i}\,d\mu = 1$ and $\int_{\Phi_L} b_i \overline{b_j}\,d\mu = 0$ for $i \neq j$; and for every cuspidal class $\pi$ the fibre $\{i : \mathrm{cls}\,i = \pi\}$ is finite and the corresponding $b_i$ span the isotypic block cut by $\mathrm{tys}_L$. Let $\varphi : G \to \mathbb{C}$ be continuous with compact support, factorizable (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`, and archimedean bi-finite of type $\mathrm{tys}_L$ (i.e. $x \mapsto \varphi(x^{-1})$ lies in the cut submodule and $\varphi$ in the dual cut submodule). Put $(A_\varphi u)(x) = \int_G u(\sigma_{\mathbb A}(x y))\,\varphi(y)\,d\mu(y)$, which is `twistedConvOp K L D σ φ u`. Then (i) for every $i$ the function $x \mapsto (A_\varphi b_i)(x)\,\overline{b_i(x)}$ is integrable on $\Phi_0$ for $\mu$, and (ii) the function sending a Hecke eigensystem $\Psi$ to $\int_{\Phi_0} \bigl\| \sum_{i\,:\,\mathrm{cls}\,i = \Psi} (A_\varphi b_i)(x)\,\overline{b_i(x)} \bigr\|\,d\mu(x)$, the inner sum being a finite sum over the fibre, is summable over all $\Psi$.
--
--   This is the trace-class statement for the $\sigma$-twisted convolution operator $A_\varphi = R(\varphi) \circ \sigma^*$ on the cuspidal spectrum of level $N$ and prescribed archimedean types, in the form needed for the kernel on the diagonal of a fundamental domain: each class contributes an integrable diagonal term and the class contributions converge in trace norm. It is used by the result that assembles the twisted trace as a sum over Hecke eigensystems of the individual class integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
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
    (hφf : IsFactorizableTestFn L φ)
    (hφU : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (hφt : IsArchBiFinite L tysL φ) :
    (∀ i, IntegrableOn (fun x => twistedConvOp K L D σ φ (b i) x * conj (b i x)) Φ₀
        (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    Summable (fun Ψ : HeckeEigensystem L ℂ =>
      ∫ x in Φ₀, ‖∑ᶠ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖
        ∂adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
