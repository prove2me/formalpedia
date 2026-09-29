-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
-- name    : AutomorphicForm.isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/df3c768b-d344-5446-a12c-3f479532b0ba
-- title:
--   Isotypic cusp forms transfer to ample Siegel windows
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{gx : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place $w$ has local height $\geq c$ and $x$-window square $\leq u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in D$. Let $\xi$ be a homomorphism from the central subgroup of the pins `productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)` — this subgroup being all of $\mathbb{A}_F^\times$ — to $\mathbb{C}^\times$; let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, $\Psi$ a Hecke eigensystem over $\mathbb{C}$, and $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying `IsIsotypicCuspFormAt` for these pins, $\xi$, $N$, $S$, $\Psi$: that is, $\varphi$ is a smooth cuspidal automorphic function at those pins (cuspidal automorphic with respect to the window $D$, the Haar measure and the conditional adelic measure on `adelicBox F`, together with $K_f$-finite smoothness), continuous, right invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, a Hecke coset eigenfunction at each $v\notin S$ with eigenvalue $\Psi.a\,v$, and satisfies $\varphi(\det(\mathrm{heckeGen}\,v)\cdot g)=(\mathrm{cNorm}\,v)^{-1}\Psi.b\,v\cdot\varphi(g)$ for $v\notin S$. Then for any reals $c',u',d_1',d_2',\kappa$ with $\kappa\geq 1$, $c'>0$, $d_1'>0$ and any finite $T'\subset\mathrm{GL}_2(\mathbb{A}_F)$, the same $\varphi$ satisfies `IsIsotypicCuspFormAt` for the pins built in the same way from the window $\bigcup_{x\in T'}\{gx: g\in \mathfrak{S}'\}$, where $\mathfrak{S}'=$ `centreCutSiegelSetAmple F c' u' d₁' d₂' κ` is the subset of the corresponding centre-cut Siegel set on which the local heights at any two infinite places differ by a factor at most $\kappa$, with the same $\xi$, $N$, $S$ and $\Psi$. No covering hypothesis, and no inequality $d_1'<d_2'$, is imposed on the second window.
--
--   This is the window-independence statement for isotypic cusp forms: once one union of right translates of a centre-cut Siegel set covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo rational points and the centre, membership in the isotypic cusp space does not depend on which finite union of translates of an ample Siegel window is used to formulate the integrability and cuspidality conditions. It is used to move an automorphic form between windows in the construction of Hecke coset systems and in the archimedean computations entering the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsIsotypicCuspFormAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (c' u' d₁' d₂' κ : ℝ) (hκ : 1 ≤ κ) (hc' : 0 < c') (hd₁' : 0 < d₁') (T' : Finset (AdelicGL2 (𝓞 F) F)) :
    IsIsotypicCuspFormAt F
      (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ := by sorry
