-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1d07aca4-7a67-57ee-90b3-689c99aa5378
-- title:
--   Casimir pair acts by scalars on a cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\}$, the corresponding union of right translates of the centre-cut Siegel set (matrices whose finite part is integral, whose local heights at all infinite places are $\ge c$, whose window quantities are $\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$), and assume `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ and some central adelic scalar $z$. Let `pins` be the production carrier data on $D$ with level subgroups $U(\mathfrak N)=\mathrm{levelOne}(\mathfrak N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ and conditioning box $\mathrm{adelicBox}$, let $\xi$ be a character of its central subgroup (which is all of $(\mathbb{A}_K)^\times$) with values in $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: $V$ is a cusp subrepresentation (contained in the $K$-finite cusp submodule for $\xi$, stable under right translation by the finite adelic subgroup and by the row-isometry subgroups at the infinite places, and stable under right convolution with factorizable archimedean bi-finite test functions), $V\neq 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$. Let $\mathfrak N\neq 0$ be an ideal of $\mathcal{O}_K$ and `tys` a family assigning to each infinite place a finite list of representations of its row-isometry subgroup, and assume the cut $V\cap\{\varphi:\varphi(gu)=\varphi(g)\ \forall u\in U(\mathfrak N)\}\cap \mathrm{archCutSubmodule}(\mathrm{tys})$ is non-zero. Let $w$ be a complex place of $K$. Then there exist $\lambda,\lambda'\in\mathbb{C}$ such that every $x\in V$ is smooth at $w$ (for each $g$, the map $e\mapsto x(g\cdot \mathrm{archComplexLiftAt}\,e)$ is $C^\infty$ on the invertible $2\times 2$ complex matrices), the first flow derivatives $\mathrm{archDerivAtComplex}\,d\,x$ in all six directions $H,E,F,iH,iE,iF$ are continuous, all second such derivatives are continuous, and the two Casimir operators at $w$, formed from $\partial_X=\tfrac12(D_X-iD_{iX})$ and $\bar\partial_X=\tfrac12(D_X+iD_{iX})$ as $-\bigl(\tfrac14\partial_H^2-\tfrac12\partial_H+\partial_E\partial_F\bigr)$ and its conjugate, satisfy $\Omega_w x=\lambda x$ and $\bar\Omega_w x=\lambda' x$.
--
--   This is Schur's lemma for the pair of Casimir operators of $\mathrm{GL}_2(\mathbb{C})$, realised at the level of functions: on an irreducible cuspidal constituent with a non-zero level-and-type cut both Casimir operators at a fixed complex place act by one scalar each, and all vectors are smooth with continuous first and second flow derivatives there. It supplies the differential equations used in the analysis of Whittaker coefficients at complex places, and is cited by the results on the expansion and on the rapid decay of those coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ lam lam' : ℂ, ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x := by sorry
