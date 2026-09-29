-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6ae78b96-afb1-5045-8669-0d2dfc1c5e0a
-- title:
--   Right convolution preserves isotypic cusp forms, principal level
-- statement:
--   Let $L$ be a number field, $\alpha,\beta$ real numbers and $\Phi_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$ a subset of the determinant slab $\{g : \|\det g\|_{\mathbb{A}_L}\in[\alpha,\beta]\}$ (with $\|\cdot\|$ the idele norm given by the module of the Haar character) which is a fundamental domain for the action of the image of $\mathrm{GL}_2(L)$ under `globalPoints` on that slab, for the adelic Haar measure `adelicGLHaar` restricted to the slab. Fix a homomorphism $\xi_L$ from the full subgroup $\top$ of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, a finite set $S$ of finite places, ideals $N_1,N$ of $\mathcal{O}_L$ all of whose prime divisors lie in $S$, and Hecke data $\Psi=(a_w,b_w)_w$ with nonzero level. Let $\varphi$ be continuous with compact support and invariant on both sides under $K(N)\cap\mathrm{GL}_2(\mathbb{A}_{L,f})$, where $K(M)$ denotes `principalLevel` at $M$ and the second factor is the kernel of the archimedean projection. Assume $v$ satisfies `IsIsotypicCuspFormAt` for the carrier data `productionPinsOf` built from $\Phi_L$, the level family $M\mapsto K(M)\cap\mathrm{GL}_2(\mathbb{A}_{L,f})$, the Hecke generators `heckeGen`, and the adelic box, at level $N_1$: that is, $v$ is a smooth cuspidal automorphic function in the sense of `IsSmoothCuspAutomorphicFnAt`, continuous, right invariant under $K(N_1)\cap\mathrm{GL}_2(\mathbb{A}_{L,f})$, a Hecke coset eigenfunction with eigenvalue $a_w$ at each $w\notin S$, and an eigenfunction of the central translation by $\det(\mathrm{heckeGen}_w)$ with eigenvalue $(\mathrm{cNorm}\,w)^{-1}b_w$ for $w\notin S$. Then the right convolution $g\mapsto\int v(gx)\varphi(x)\,d\mu(x)$ satisfies the same predicate with $N_1$ replaced by $N$, the data $\xi_L,S,\Psi$ unchanged.
--
--   This is the statement that the Hecke algebra of continuous compactly supported bi-$K(N)$-invariant test functions acts on the space of cuspidal automorphic forms with prescribed central data and prescribed Hecke eigenvalues outside $S$, in the edition of the set-up where the level family consists of the principal congruence subgroups $K(M)$. It is used to produce elements of the isotypic cusp submodule cut out by an archimedean condition, and in the bounds for convolution operators against orthonormal families in that submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (N₁ N : Ideal (𝓞 L)) (hN₁ : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₁ → w ∈ S)
    (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S)
    (Ψ : HeckeEigensystem L ℂ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (v : AdelicGL2 (𝓞 L) L → ℂ)
    (hv : IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N₁ S Ψ v) :
    IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N S Ψ (rightConv L v φ) := by sorry
