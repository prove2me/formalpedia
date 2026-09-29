-- Prove2me | Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
-- name    : AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/77051918-48df-55c4-bc51-eeaa749bec11
-- title:
--   Finite-dimensionality of isotypic cusp spaces of fixed archimedean type
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\,(\,\cdot\,x)\bigl(\text{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\bigr)$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite part lies in `finiteIntegralGL2` and which satisfy, at every infinite place $w$, $c\le\mathrm{localHeight}$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$; assume `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g\,\mathrm{diag}(z,z)\in D$. Let `pins` be `productionPinsOf` for $D$, the level subgroups $N\mapsto \text{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \text{heckeGen}(v)$ and the box `adelicBox F` (Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup $\top$, adelic measure conditioned on the box). Fix a character $\xi$ of `pins.Z` with values in $\mathbb{C}^\times$, a nonzero ideal $N$ of $\mathcal{O}_F$, a finite set $S$ of finite places, an archimedean type family `tys` (at each infinite place $w$ a finite list of representations `ArchRepAt`), and a Hecke eigensystem $\Psi$ over $\mathbb{C}$. Then the intersection of `isotypicCuspSubmodule F pins ξ N S Ψ` — the $\mathbb{C}$-span of the continuous functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_F)$ that are smooth cuspidal automorphic at these pins with central character $\xi$, invariant under right translation by the level-$N$ subgroup, Hecke coset eigenfunctions with eigenvalue $\Psi.a(v)$ for $v\notin S$, and satisfy $\varphi(\mathrm{diag}(\det\text{heckeGen}(v))\,g)=\Psi.\mathrm{toRawCentral}.b(v)\,\varphi(g)$ for $v\notin S$ — with `archCutSubmodule F tys`, the infimum over infinite places $w$ of the supremum of the submodules `archTypeSubmoduleAt F w (tys.rep w i)`, is a finite-dimensional $\mathbb{C}$-vector space.
--
--   This is the finiteness theorem for spaces of cusp forms on $\mathrm{GL}_2$ over a number field with prescribed central character, level, Hecke eigenvalues away from a finite set of places, and finitely many archimedean types. It is obtained by bounding the space by a finite supremum of cuspidal constituents, each of whose level-invariant, archimedean-type-cut part is finite-dimensional, and it supports the later construction of finite families of convolution operators and of trace and Whittaker-coefficient statements for such cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

theorem AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ) :
    FiniteDimensional ℂ
      ↥(isotypicCuspSubmodule F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ
        ⊓ archCutSubmodule F tys) := by sorry
