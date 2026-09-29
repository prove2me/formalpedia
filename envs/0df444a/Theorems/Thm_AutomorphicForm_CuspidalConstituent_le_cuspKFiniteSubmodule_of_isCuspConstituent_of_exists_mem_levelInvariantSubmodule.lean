-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
-- name    : AutomorphicForm.CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/8a28693b-f4bc-5a57-bda7-8e70a406a2ff
-- title:
--   Window-independence of the K-finite cuspidal space of a constituent
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, $d_1>0$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $W=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}(c,u,d_1,d_2)\}$, where $\mathfrak{S}(c,u,d_1,d_2)$ is the centre-cut Siegel set of elements whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; assume $W$ covers modulo the centre, i.e. for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,\mathrm{diag}(z,z)\in W$. Let $P_W$ be the production pins over $W$, with Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup $Z=\top$, level groups $N\mapsto \mathrm{levelOne}(N)\cap \mathrm{GL}_2(\mathbb{A}_F)_{\mathrm{fin}}$, Hecke generators $v\mapsto \mathrm{heckeGen}(v)$, and the adelic measure conditioned on `adelicBox`. Let $\xi : Z\to\mathbb{C}^\times$ be a character and $V$ a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cusp constituent at $(P_W,\xi)$: $V$ is non-zero, contained in `cuspKFiniteSubmodule` (the span of the continuous $\varphi$ all of whose right translates are smooth cuspidal automorphic at $(P_W,\xi)$ and which lie in the archimedean cut submodule for some archimedean type family), stable under right translation by finite-adelic elements and by the archimedean row-isometry subgroups, stable under right convolution by factorizable archimedean-bi-finite test functions, and minimal with these properties. Assume further that for some non-zero ideal $N$ of $\mathcal{O}_F$ there is a non-zero $\varphi\in V$ which is right invariant under $\mathrm{levelOne}(N)\cap\mathrm{GL}_2(\mathbb{A}_F)_{\mathrm{fin}}$. Then for all reals $c',u',d_1',d_2'$ with $c'>0$ and $d_1'>0$ and every finite $T'\subset\mathrm{GL}_2(\mathbb{A}_F)$ — no covering condition, no inequality $d_1'<d_2'$, and no relation to the unprimed data — $V$ is contained in the $K$-finite smooth cuspidal submodule at the production pins over $W'=\bigcup_{x\in T'}\{g x : g\in\mathfrak{S}(c',u',d_1',d_2')\}$ with the same character $\xi$.
--
--   The statement expresses that membership in the $K$-finite smooth cuspidal space does not depend on the Siegel window chosen to define the pins, once the constituent contains one non-zero vector invariant under some level group: moderate-growth and cuspidality estimates on one covering window propagate to every other window. It is used in the comparison of cuspidal constituents attached to different windows, and is cited in the proof that a cuspidal constituent is determined by the data it meets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (hVN : ∃ φ ∈ V, φ ≠ 0 ∧ φ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    V ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by sorry
