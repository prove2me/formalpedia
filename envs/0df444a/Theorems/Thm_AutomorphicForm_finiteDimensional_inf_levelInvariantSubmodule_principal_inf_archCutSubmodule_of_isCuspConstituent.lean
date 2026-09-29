-- Prove2me | Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent
-- name    : AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f0407665-66c9-51fd-95ad-2990bedfbaa0
-- title:
--   Admissibility of a cuspidal constituent at principal level
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{g x: g\in \Sigma\}$, where $\Sigma$ is the centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂`, consisting of those $g$ whose finite part lies in the integral subgroup, whose archimedean component at each infinite place $w$ has local height at least $c$ and squared $x$-window at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every $w$. Assume `CoversModCentre`: for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\, z\in D$. Let `pins` be the carrier data `productionPinsOf` attached to $D$, to the level subgroups $N\mapsto K(N)\cap \mathrm{GL}_2(\mathbb{A}_F)_{\mathrm{fin}}$ given by `principalLevel`, to the Hecke generators `heckeGen`, and to the box `adelicBox`; its central subgroup is all of $\mathbb{A}_F^\times$, and $\xi$ is a homomorphism from it to $\mathbb{C}^\times$. Let $N\neq 0$ be an ideal of $\mathcal{O}_F$, let `tys` assign to each infinite place $w$ finitely many archimedean types, and let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cuspidal constituent for `pins` and $\xi$: $V$ lies in the cuspidal $K$-finite submodule, is stable under right translation by the finite-adelic subgroup and by the row-isometry subgroups at the infinite places and under right convolution by factorizable archimedean-bi-finite test functions, is non-zero, and contains no such stable subspace other than $0$ and $V$. Then the subspace of $V$ consisting of functions invariant under right multiplication by $K(N)\cap\mathrm{GL}_2(\mathbb{A}_F)_{\mathrm{fin}}$ and lying in $\bigsqcap_w\bigsqcup_{i<\mathrm{card}(w)}$ of the archimedean type submodules of `tys` is finite-dimensional over $\mathbb{C}$. No positivity is assumed on $c$ or $d_1$.
--
--   This is admissibility of a cuspidal constituent, read at the principal congruence level $K(N)$ and a prescribed finite family of archimedean types: the space of $K(N)$-invariant vectors of those types is finite-dimensional. It is used downstream to produce, for vectors in such a cut, expressions as finite sums of right convolutions and eigenvector statements for the archimedean Casimir operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent.lean

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

theorem AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ V) :
    FiniteDimensional ℂ
      ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) N ⊓ archCutSubmodule F tys) := by sorry
