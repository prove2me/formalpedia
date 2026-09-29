-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- name    : AutomorphicForm.exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/28866614-541a-5cf6-a7e7-59a25d45c15f
-- title:
--   Cyclicity of the isotypic cusp space under right convolution
-- statement:
--   Let $L/K$ be an extension of number fields, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_L)$. Write $D=\bigcup_{x\in T}\,(\cdot\,x)\bigl(\mathtt{centreCutSiegelSet}\,L\,c\,u\,d_1\,d_2\bigr)$, the union of the right translates by elements of $T$ of the set of $g$ whose finite part is integral, whose archimedean components have local height $\ge c$ at every infinite place, squared $x$-window $\le u^2$ at every infinite place, and archimedean determinant norm in $[d_1,d_2]$ at every infinite place. Assume `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_L)$ admits $\gamma\in\mathrm{GL}_2(L)$ and $z\in\mathbb{A}_L^\times$ with $\gamma g\,z\in D$. Let $\xi$ be a homomorphism to $\mathbb{C}^\times$ from the centre group of the production pins of $L$ attached to $D$, the level family $N\mapsto \mathtt{levelOne}(N)\cap\ker(\mathtt{glArch})$, the Hecke generators $v\mapsto\mathtt{heckeGen}(v)$ and the adelic box (that centre group being all of $\mathbb{A}_L^\times$, the measures being the adelic Haar measure on $\mathrm{GL}_2$ and the box-conditioned additive Haar measure). Let $N_K$ be an ideal of $\mathcal{O}_K$, $S_K$ a finite set of primes of $K$ containing every prime dividing $N_K$, $S_L$ a finite set of primes of $L$, $\Psi$ a Hecke eigensystem of $L$ over $\mathbb{C}$ (a nonzero level together with families $a,b$ indexed by the primes of $L$), and $\mathrm{tys}$ an archimedean type family of $L$ (cardinalities $\mathrm{card}(w)$ and representations $\mathrm{rep}(w,i)$ at each infinite place $w$). Put $W$ for the intersection of the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for these pins, $\xi$, the level $N_K\mathcal{O}_L$, $S_L$ and $\Psi$ with $\mathtt{archCutSubmodule}$, the infimum over infinite places $w$ of the supremum over $i<\mathrm{card}(w)$ of the archimedean type submodules of $\mathrm{rep}(w,i)$. Then for every nonzero $w\in W$ and every $w'\in W$ there are a finite set $s$ of functions $\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ and coefficients $a(\varphi)\in\mathbb{C}$ such that each $\varphi\in s$ is continuous, compactly supported and satisfies `IsUnitFactorizableAboveOfType` for $K,L,\mathrm{tys}$, the subgroup $\mathtt{levelOne}(N_K\mathcal{O}_L)\cap\ker(\mathtt{glArch})$ and $S_K$ (that is, it is unit-factorizable above $K$ for these data and archimedean bi-finite of type $\mathrm{tys}$), and $w'=\sum_{\varphi\in s} a(\varphi)\,(w*\varphi)$, where $w*\varphi$ denotes the right convolution $\mathtt{convOp}\,L\,\varphi\,w$.
--
--   This is the cyclicity statement for isotypic cusp spaces on $\mathrm{GL}_2$ over a number field: a single nonzero isotypic cusp form, cut by an archimedean type family, generates the whole space under right convolution by continuous compactly supported test functions of the unit-factorizable class above $K$. It is obtained from the decomposition of the isotypic-and-arch-cut space into cuspidal constituents together with cyclicity inside a constituent, and is used in the version of the statement formulated for a fundamental domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (w w' : AdelicGL2 (𝓞 L) L → ℂ) (hw : w ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys) (hw0 : w ≠ 0)
    (hw' : w' ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
        w' = ∑ φ ∈ s, a φ • convOp L φ w := by sorry
