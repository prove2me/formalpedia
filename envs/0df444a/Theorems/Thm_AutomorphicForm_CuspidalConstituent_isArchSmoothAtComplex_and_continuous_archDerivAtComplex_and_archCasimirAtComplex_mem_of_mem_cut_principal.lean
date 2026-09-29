-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut_principal
-- name    : AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7d3f8d1c-5d63-5bb0-87c1-71d194d848ba
-- title:
--   Smoothness and Casimir stability of cut vectors at principal level
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Put $D=\bigcup_{x\in T}\{g x: g\in\text{centreCutSiegelSet}\}$, where `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2` and which satisfy, at every infinite place $w$, $c\le\mathrm{localHeight}$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$; assume `CoversModCentre K D`, i.e. every adelic $g$ can be brought into $D$ by left multiplication by a global point of $\mathrm{GL}_2(K)$ and right multiplication by a central adelic scalar. Let `pins` be the production carrier data on $D$ with level family $N\mapsto \text{principalLevel}(N)\sqcap\text{finiteAdelicGL2Subgroup}$, Hecke elements $v\mapsto \mathrm{heckeGen}(v)$ and adelic box `adelicBox K`, let $\xi$ be a character of `pins.Z` with values in $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: $V$ is a cusp subrepresentation (contained in the $K$-finite cusp submodule for $\xi$, stable under right translation by the finite-adelic subgroup and by the archimedean row-isometry subgroups, and stable under right convolution by factorizable archimedean bi-finite test functions), $V\ne 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$. Let $N$ be a nonzero ideal of $\mathcal{O}_K$, `tys` a family of archimedean types, $w$ a complex infinite place, and let $x$ lie in the cut $X=V\sqcap\{\varphi:\varphi(gu)=\varphi(g)\ \forall g,\ \forall u\in\text{principalLevel}(N)\sqcap\text{finiteAdelicGL2Subgroup}\}\sqcap\text{archCutSubmodule}(\mathrm{tys})$. Then: $x$ is smooth at $w$ in the sense that for every $g$ the function $e\mapsto x(g\cdot \text{archComplexLiftAt}(e))$ is $C^\infty$ over $\mathbb{R}$ on the set of invertible complex $2\times2$ matrices $e$; for each of the six directions $d$ in `ArchDirComplex` the derivative $\text{archDerivAtComplex}\,d\,x$ is continuous; for each pair $d,d'$ the iterated derivative is continuous; and both $\text{archCasimirAtComplex}\,x$ and $\text{archCasimirBarAtComplex}\,x$, the Casimir combinations of the holomorphic and antiholomorphic directional operators at $w$, again lie in $X$.
--
--   This is the principal-level version of the statement that the cut of a cuspidal constituent by a level-$\text{principalLevel}(N)$ invariance condition and a prescribed family of archimedean $K$-types consists of vectors smooth at a complex place and is preserved by the two Casimir operators attached to that place. It is used in the construction of eigenvectors for the archimedean Casimir action on such cuts, namely by [`AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent_principal`](thm.html#AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut_principal
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
      archCasimirBarAtComplex hw x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys := by sorry
