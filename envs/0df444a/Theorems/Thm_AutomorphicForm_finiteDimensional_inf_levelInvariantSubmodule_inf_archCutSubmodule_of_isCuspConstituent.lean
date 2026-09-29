-- Prove2me | Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
-- name    : AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/e9bab758-e20c-574c-a902-b312e2bff076
-- title:
--   Finite-dimensionality of level and archimedean cuts of cuspidal constituents
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part is integral, whose archimedean component at every infinite place $w$ has local height at least $c$ and squared $x$-window at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo $\mathrm{GL}_2(F)$ on the left and central ideles on the right. Let `pins` be `productionPinsOf` for this $D$, with level groups $U(M)=\mathrm{levelOne}(M)\cap\mathrm{GL}_2(\mathbb{A}_{F,\mathrm{fin}})$, Hecke generators $\mathrm{heckeGen}_v$, and the adelic box (giving the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup $\top$, and the conditioned additive adelic measure); let $\xi$ be a character of that central subgroup into $\mathbb{C}^\times$. Let $N\neq 0$ be an ideal of $\mathcal{O}_F$, `tys` a family of archimedean types, and $V$ a submodule of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_F)$ which is a cuspidal constituent: a nonzero cusp subrepresentation (contained in the $K$-finite cusp submodule, stable under right translation by the finite part and by the archimedean row-isometry subgroups, and under right convolution by factorizable, archimedean bi-finite test functions) admitting no cusp subrepresentation other than $0$ and itself. Then the intersection of $V$ with the submodule of functions right invariant under $U(N)$ and with $\bigsqcap_w\bigsqcup_i$ of the archimedean type submodules attached to `tys` is a finite-dimensional $\mathbb{C}$-vector space.
--
--   This is the admissibility statement for cuspidal constituents in adelic form: a constituent has only finitely many vectors of fixed finite level and fixed archimedean type. It is the finiteness input used downstream for Hecke-module arguments, and is cited in the construction of eigenvectors and in decompositions of isotypic cusp spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ V) :
    FiniteDimensional ℂ
      ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) N ⊓ archCutSubmodule F tys) := by sorry
