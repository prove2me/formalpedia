-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite
-- name    : AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/42e74905-c5be-5b21-9b58-9ffd82dd41d2
-- title:
--   Smoothed cuspidal member is K-finite at Siegel pins
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $d_1>0$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$. Let $\alpha,\beta$ be reals and $\Phi_0$ a set satisfying `IsSlabFundamentalDomain`, i.e. $0<\alpha<\beta$, $\Phi_0$ lies in the slab where the idele norm of the determinant is in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of the global points acting on the adelic $\mathrm{GL}_2$ Haar measure restricted to that slab. Let $tys$ assign to each infinite place a finite family of archimedean representation types, and let $f$ be factorizable (a product of an archimedean test factor on the archimedean component with a finite test factor on the finite component) and archimedean bi-finite for $tys$ (that is, $x\mapsto f(x^{-1})$ lies in `archCutSubmodule F tys` and $f$ lies in `archDualCutSubmodule F tys`). Let $\varphi$ be continuous and smooth-cuspidal-automorphic at the pins of $\Phi_0$ with central character $\xi$. Then the right convolution $g\mapsto\int \varphi(gx)f(x)\,dx$ against the Haar measure lies in `cuspKFiniteSubmodule` for the production pins whose domain is $W=\bigcup_{x\in T}\mathfrak{S}\cdot x$, $\mathfrak{S}$ being the centre-cut Siegel set (finite part integral, local heights $\ge c$, $x$-window squares $\le u^2$, archimedean determinant norms in $[d_1,d_2]$), whose centre is the full subgroup, whose level subgroups are $N\mapsto$ `levelOne` intersected with the kernel of the archimedean projection, whose Hecke elements are `heckeGen` at each finite place, and whose additive measure is the Haar measure of the adeles conditioned on the adelic box; that is, the convolution is continuous, has archimedean types in $tys$, and every right translate of it is smooth-cuspidal-automorphic with character $\xi$ and square-integrable over $W$. No hypothesis relates $T$, $u$, $d_2$ to a covering of the fundamental domain.
--
--   This is the smoothing step in the spectral analysis of the cuspidal part: convolution with an archimedean bi-finite factorizable test function turns a merely continuous cuspidal member into a $K$-finite cusp function of prescribed archimedean types, uniformly square-integrable over finite unions of translated Siegel sets. It is used in the construction of nonzero $K$-finite vectors in closed cuspidal subrepresentations and in the identification of such subrepresentations with subrepresentations of the $K$-finite cusp space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    rightConv F φ f ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by sorry
