-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule
-- name    : AutomorphicForm.exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/9d6428fe-6459-53ed-809d-db6771d744a7
-- title:
--   Composing convolution operators on isotypic cusp forms
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and work on $\mathrm{GL}_2$ of the adele ring, `AdelicGL2 (𝓞 L) L`. Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T$ of adelic matrices, and let $D=\bigcup_{x\in T}\{g\cdot x\}$ be the union of the right translates by $T$ of the centre-cut Siegel set `centreCutSiegelSet L c u d₁ d₂`, i.e. of the $g$ whose finite part is integral, whose archimedean component at every infinite place has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume $D$ satisfies `CoversModCentre`: each $g$ admits $\gamma\in\mathrm{GL}_2(L)$ and $z\in\mathbb{A}_L^\times$ with $\gamma g\,z\in D$ (global points on the left, central adelic scalar on the right). Let $\xi$ be a homomorphism to $\mathbb{C}^\times$ from the group $Z$ of the pins `productionPinsOf L D (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v) (adelicBox L)`, whose ingredients are the adelic Haar measure and Borel structure on $\mathrm{GL}_2(\mathbb{A}_L)$, the window $D$, the group $Z=\top$ (so $\xi$ is a character of $\mathbb{A}_L^\times$), the level family attaching to $N$ the intersection of `levelOne (𝓞 L) L N` with the kernel $\ker(\mathrm{glArch})$ of the archimedean-component map, the Hecke generators `heckeGen`, and additive Haar measure conditioned on the adelic box. Let $N_K$ be an ideal of $\mathcal{O}_K$, $S_K$ a finite set of primes of $K$ containing every prime dividing $N_K$, $S_L$ a finite set of primes of $L$, $\Psi$ a Hecke eigensystem for $L$ with complex coefficients (a nonzero level ideal together with families $a_v,b_v$), and $\mathrm{tys}$ an archimedean type family for $L$ (for each infinite place $w$, a finite list `tys.rep w` of archimedean representation data). Finally let $\varphi,\psi$ be functions on $\mathrm{GL}_2(\mathbb{A}_L)$ that are continuous, compactly supported, and satisfy `IsUnitFactorizableAboveOfType K L tys` at the subgroup $\mathrm{levelOne}(N_K\mathcal{O}_L)\cap\ker(\mathrm{glArch})$ and the place set $S_K$, i.e. `IsUnitFactorizableAbove K L` for those data together with `IsArchBiFinite L tys`. The conclusion is the existence of a finite set $s$ of functions on $\mathrm{GL}_2(\mathbb{A}_L)$, each again continuous, compactly supported and of the same unit-factorizable type, and of complex coefficients $a$, such that for every $w$ lying in the intersection of `archCutSubmodule L tys` (the infimum over infinite places $w$ of the supremum of the archimedean type submodules attached to the members of `tys.rep w`) with the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for the above pins, $\xi$, the level $N_K\mathcal{O}_L$, $S_L$ and $\Psi$, one has $\mathrm{convOp}\,\psi(\mathrm{convOp}\,\varphi\,w)=\sum_{\chi\in s}a(\chi)\,\mathrm{convOp}\,\chi\,w$, where $\mathrm{convOp}\,f$ sends $w$ to the right convolution `rightConv L w f`.
--
--   The statement expresses that the span of the right convolution operators by continuous, compactly supported, unit-factorizable test functions of a fixed archimedean type is closed under composition when restricted to the space of isotypic cusp forms cut out by an archimedean type family; this is what allows that span to be treated as an algebra of operators on the relevant space of automorphic forms. It is used in [`AutomorphicForm.exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain`](thm.html#AutomorphicForm.exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule.lean

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

theorem AutomorphicForm.exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (φ ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      Continuous φ ∧ HasCompactSupport φ)
    (hψ : IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK ψ ∧
      Continuous ψ ∧ HasCompactSupport ψ) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
        ∀ w ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys,
          convOp L ψ (convOp L φ w) = ∑ χ ∈ s, a χ • convOp L χ w := by sorry
