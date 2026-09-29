-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_principal_le_isotypicCuspSubmodule_principal_of_le_of_ne_bot
-- name    : AutomorphicForm.isotypicCuspSubmodule_principal_le_isotypicCuspSubmodule_principal_of_le_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e717b6ad-4108-5e87-b1a1-a70deb659cb7
-- title:
--   Raising the determinant floor does not enlarge isotypic cusp spaces
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,d_1'$ be real numbers and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, with $0<c$, $d_1\le d_1'$, $0<d_1'$ and $d_1'<d_2$. For a floor $d$ write $W(d)=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\}$, where the centre-cut Siegel set consists of those $g\in\mathrm{GL}_2(\mathbb{A}_F)$ whose finite part lies in the integral subgroup $\mathrm{finiteIntegralGL2}$, with $\mathrm{localHeight}\ge c$ and $\mathrm{xWindowSq}\le u^2$ at the archimedean component at every infinite place, and with $\mathrm{archDetNorm}_w(g)\in[d,d_2]$ for every infinite place $w$. Assume $W(d_1)$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo global points and the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g z\in W(d_1)$. Let $\xi$ be a homomorphism to $\mathbb{C}^\times$ from the central subgroup of the production pins (which is all of $\mathbb{A}_F^\times$), those pins carrying the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the domain $W(d_1)$, the level family $N\mapsto \mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}_v$, and additive Haar measure conditioned on $\mathrm{adelicBox}$. Fix an ideal $N\subseteq\mathcal{O}_F$, a finite set $S$ of finite places and a Hecke eigensystem $\Psi$ over $\mathbb{C}$. If the isotypic cusp submodule for the pins with domain $W(d_1)$ — the $\mathbb{C}$-span of the continuous, right $\bigl(\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})\bigr)$-invariant smooth cuspidal automorphic functions with Hecke eigenvalue $\Psi.a\,v$ and central eigenvalue $\Psi.b\,v$ for $v\notin S$ — is non-zero, then the corresponding submodule for the pins with domain $W(d_1')$ is contained in it.
--
--   This is the transport of square-integrability between two centre-cut Siegel windows differing only in the lower determinant bound, at principal congruence level: once the space attached to the wider window $W(d_1)$ is non-zero, its central character is contracting enough that every isotypic cusp form which is $L^2$ on $W(d_1')$ is already $L^2$ on $W(d_1)$. It feeds the finite spectral expansion of isotypic cusp forms at principal level, [`AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule`](thm.html#AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_principal_le_isotypicCuspSubmodule_principal_of_le_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isotypicCuspSubmodule_principal_le_isotypicCuspSubmodule_principal_of_le_of_ne_bot
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (hne : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≠ ⊥) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤
      isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ := by sorry
