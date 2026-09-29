-- Prove2me | Theorems.Thm_AutomorphicForm_exists_archTypeFamily_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot
-- name    : AutomorphicForm.exists_archTypeFamily_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/52b65064-e7a6-5e85-a498-97e747b978fd
-- title:
--   Nonzero isotypic cusp spaces contain vectors of finite archimedean type
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $d_1>0$ (no relation between $d_1$ and $d_2$ is imposed), and let $T$ be a finite subset of $G=\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\mathfrak{S}x$, where $\mathfrak{S}$ is the set of $g\in G$ whose finite part lies in `finiteIntegralGL2`, whose component at each infinite place $w$ has local height at least $c$ and window coordinate satisfying $\mathrm{xWindowSq}\le u^{2}$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every $w$; assume $D$ covers $G$ modulo rational points and the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g\,\mathrm{diag}(z,z)\in D$. Fix the carrier data `productionPinsOf` attached to $D$, to the levels $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the Hecke elements $\mathrm{heckeGen}(v)$ and to the box `adelicBox F` (so the central subgroup is all of $\mathbb{A}_F^\times$, the measures being adelic Haar measure on $G$ and Haar measure on $\mathbb{A}_F$ conditioned on the box). Let $\xi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$, let $N\neq 0$ be an ideal of $\mathcal{O}_F$, let $S$ be a finite set of maximal ideals, and let $\Psi$ be a Hecke eigensystem over $\mathbb{C}$ (a level ideal $\neq 0$ together with eigenvalues $a_v,b_v$). Assume the isotypic cusp submodule $V$ — the $\mathbb{C}$-span of the continuous smooth cuspidal automorphic functions $\varphi$ with central character $\xi$ that are right invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, are Hecke coset eigenfunctions with eigenvalue $\Psi.a_v$ for all $v\notin S$, and satisfy $\varphi(\mathrm{diag}(\det \mathrm{heckeGen}(v))g)=\Psi.b_v\varphi(g)$ for $v\notin S$ — is nonzero. Then there exists an archimedean type family $\mathrm{tys}$, given by a cardinality $\mathrm{card}(w)\in\mathbb{N}$ and representations $\mathrm{rep}(w,i)$ for each infinite place $w$ and $i<\mathrm{card}(w)$, such that $V\cap\bigcap_w\sum_{i}\mathrm{archTypeSubmoduleAt}(w,\mathrm{rep}(w,i))$ is nonzero.
--
--   This is the passage from a nonzero space of cusp forms to a nonzero subspace of vectors of finite type under the maximal compact subgroups at the infinite places ($K_\infty$-finite vectors), the usual first step towards the Harish-Chandra module of an automorphic representation; it is obtained by convolution with a suitable factorizable test function. It is used in the construction of cuspidal constituents and in the trace and class-sum growth estimates of the automorphic side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_archTypeFamily_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

theorem AutomorphicForm.exists_archTypeFamily_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (hne : isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N S Ψ ≠ ⊥) :
    ∃ tys : AutomorphicForm.ArchTypeFamily F,
      isotypicCuspSubmodule F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ
        ⊓ archCutSubmodule F tys ≠ ⊥ := by sorry
