-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep
-- name    : AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ad9c3e6d-5f5f-556a-b9cd-dcc4f0d87bb0
-- title:
--   Archimedean type cuts inside a cuspidal subrepresentation refine to irreducibles
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, let $\xi$ be a character of the full unit group $(\mathbb{A}_F)^\times$ (the subgroup $\top$) with values in $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_F$, and let $\mathrm{tys}$ be an archimedean type family, i.e. for each infinite place $w$ a number $\mathrm{card}\,w$ of data $\mathrm{rep}\,w\,i$, each consisting of a dimension $n$ and a representation of the connected row-isometry group of $F_w$ on $\mathbb{C}^n$. Fix the carrier data `productionPinsOf` built from: the domain $\bigcup_{x\in T}\,\mathfrak{S}\cdot x$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of the $g$ whose finite part is integral, whose archimedean components at every infinite place have local height $\ge c$, $x$-window square $\le u^2$ and archimedean determinant norm in $[d_1,d_2]$; the level subgroups $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup` (the kernel of the archimedean projection); the Hecke elements `heckeGen v`; the central subgroup $\top$; the Borel Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$; and the additive adelic Haar measure conditioned on `adelicBox`. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying `IsCuspSubrep` for these pins and $\xi$: $V$ lies in the span of the continuous functions all of whose right translates are smooth cuspidal automorphic at the pins with central character $\xi$ and which lie in some archimedean type cut, and $V$ is stable under right translation by the finite-adelic subgroup, under right translation by row isometries at each infinite place, and under right convolution by factorizable test functions that are archimedean bi-finite. Then there are a natural number $n$ and families $\tau_1,\dots,\tau_n$, each assigning to every infinite place $w$ a datum $\tau_j(w)$ whose representation is irreducible, such that $$V\sqcap \mathcal{A}^{U(N)}\sqcap \mathcal{A}[\mathrm{tys}]\ \le\ \bigsqcup_{j=1}^{n} V\sqcap \mathcal{A}^{U(N)}\sqcap \mathcal{A}[\tau_j],$$ where $\mathcal{A}^{U(N)}$ is the submodule of functions invariant under right multiplication by the level group at $N$, $\mathcal{A}[\mathrm{tys}]=\bigsqcap_w\bigsqcup_{i<\mathrm{card}\,w}$ `archTypeSubmoduleAt F w (tys.rep w i)`, and $\mathcal{A}[\tau_j]$ is the same cut for the family with exactly one datum $\tau_j(w)$ at each place.
--
--   This is the refinement step that replaces a cut by an arbitrary finite list of archimedean types by a finite sum of cuts by single irreducible types, using complete reducibility of finite-dimensional continuous representations of the compact row-isometry groups together with a Jordan–Hölder argument. It is used in the passage from cuspidal subrepresentations to eigenvector capture for right convolution, where the dichotomy is run one irreducible archimedean type at a time.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep.lean

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

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ (n : ℕ) (τs : Fin n → ∀ w : InfinitePlace F, ArchRepAt F w),
      (∀ j w, (τs j w).ρ.IsIrreducible) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
        ⨆ j : Fin n, V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F) := by sorry
