-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
-- name    : AutomorphicForm.CuspidalConstituent.comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/bac0238b-2dca-53fc-b74f-122ebf830afc
-- title:
--   J-stability of a cuspidal constituent at a real place
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite component lies in `finiteIntegralGL2`, whose archimedean component has local height at least $c$ and $x$-window square at most $u^2$ at every infinite place, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume `CoversModCentre` for $D$: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g\,z\in D$ (the image of $\gamma$ under `globalPoints` and the central scalar attached to $z$). Let `pins` be `productionPinsOf` for this $D$, with level groups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}(v)$, and conditioning set `adelicBox` $F$; its Borel structures and measures are the adelic Haar data, and its central subgroup is all of $\mathbb{A}_F^\times$. Let $\xi$ be a character of that subgroup into $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of height-one primes, $\Psi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a,b$ indexed by the primes), and $V$ a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$. Assume $V$ is a cuspidal constituent for `pins` and $\xi$, i.e. $V$ satisfies the predicate `IsCuspSubrep`, $V\neq 0$, and every `IsCuspSubrep` submodule contained in $V$ is $0$ or $V$; and assume $V$ meets the cut $(N,S,\Psi)$, i.e. $V$ contains some $\varphi\neq 0$ satisfying `IsIsotypicCuspFormAt` for $N$, $S$, $\Psi$. Finally let $w$ be a real infinite place of $F$ and $x\in V$. Then the function $g\mapsto x(g\cdot \mathrm{archRealGLAt}\,h_w\,J)$ again lies in $V$, where `UpperHalfPlane.J` is the element of $\mathrm{GL}_2(\mathbb{R})$ of determinant $-1$ and `archRealGLAt` places it in the adelic group at $w$ through the identification of $F_w$ with $\mathbb{R}$.
--
--   The stability of a cuspidal constituent under right translation by the determinant $-1$ element at a real place: since the archimedean stability built into the cusp-subrepresentation predicate only involves the determinant-one rotation group at $w$, this translate has to be produced by uniqueness of the constituent attached to a Hecke cut. It feeds the reflection and lowering arguments for isotypic cusp forms, the computation of the archimedean parameter occurring in a constituent, and the existence statement for constituents used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (hmeet : CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V) :
    (fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ V := by sorry
