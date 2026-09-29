-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isotypicCuspSubmodule_le_cuspMemberSubmodule
-- name    : AutomorphicForm.CuspidalSpectrum.isotypicCuspSubmodule_le_cuspMemberSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/89b64002-e087-5bf8-8b48-17a58ed61214
-- title:
--   Isotypic cusp forms lie in the slab cusp-member submodule
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $F$. Write $W=\bigcup_{x\in T}\{g x : g\in\mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` is the set of $g$ whose finite part is integral, whose archimedean component at each infinite place has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$. Assume `CoversModCentre F W`: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in W$. Let $\xi$ be a homomorphism from the full group of idele units to $\mathbb C^\times$, let $N$ be an ideal of $\mathcal O_F$, $S$ a finite set of finite places, $\Psi$ a Hecke eigensystem over $\mathbb C$ (a nonzero level ideal together with families $a,b$ indexed by the finite places), and let $\Phi_0$ satisfy `IsSlabFundamentalDomain F α β Φ₀`, i.e. $0<\alpha<\beta$, $\Phi_0$ is contained in the determinant-norm slab for $\alpha,\beta$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on adelic $\mathrm{GL}_2$-Haar measure restricted to that slab. Then the span of the functions satisfying `IsIsotypicCuspFormAt` for the carrier data `productionPinsOf` with window $W$, level subgroups $\mathrm{levelOne}(N)\cap\ker(\text{archimedean part})$, Hecke generators at each finite place, and box $\mathrm{adelicBox}\,F$, with character $\xi$, level $N$, places $S$ and eigensystem $\Psi$, is contained in `cuspMemberSubmodule F Φ₀ ξ`, the space of continuous $\varphi$ that are smooth cuspidal automorphic functions for the carrier data attached to $\Phi_0$ and the character $\xi$.
--
--   This is the transport step of reduction theory in measure-theoretic form: automorphy and the membership conditions imposed on a finite union of translates of a centre-cut Siegel set covering $\mathrm{GL}_2(\mathbb A_F)$ modulo the rational points and the centre are inherited on any fundamental domain for a determinant-norm slab. It moves isotypic cusp forms from the window, where the Hecke conditions are formulated, into the space on a slab fundamental domain, and is used in the finite decomposition of isotypic cusp spaces under the smoothing operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isotypicCuspSubmodule_le_cuspMemberSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.isotypicCuspSubmodule_le_cuspMemberSubmodule
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤ cuspMemberSubmodule F Φ₀ ξ := by sorry
