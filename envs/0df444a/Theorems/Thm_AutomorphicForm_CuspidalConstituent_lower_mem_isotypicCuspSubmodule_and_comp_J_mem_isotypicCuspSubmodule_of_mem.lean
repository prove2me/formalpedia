-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
-- name    : AutomorphicForm.CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/4bb77592-00f8-5790-a1a7-53854f1b5491
-- title:
--   Lowering operator and J-translate stay isotypic in a cuspidal constituent
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $F$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part is integral, and for which at every infinite place the local height is at least $c$, the $x$-window square is at most $u^2$, and the archimedean determinant norm lies in $[d_1,d_2]$; let `pins` be `productionPinsOf` applied to $D$, to the level subgroups $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, to the Hecke generators $v\mapsto$ `heckeGen`, and to `adelicBox F`, so that in particular its central subgroup is the whole unit group, and let $\xi$ be a homomorphism from that subgroup to $\mathbb C^\times$. Fix an ideal $N$, a finite set $S$ of height-one primes of $\mathcal O_F$, a Hecke eigensystem $\Psi$ over $\mathbb C$ (a level ideal $\neq\bot$ together with families $a_v,b_v$), and a $\mathbb C$-submodule $V$ of the complex-valued functions on $\mathrm{GL}_2$ of the adeles which is a cuspidal constituent for `pins` and $\xi$, i.e. a cusp subrepresentation with $V\neq\bot$ that is minimal in the sense that every cusp subrepresentation contained in it is $\bot$ or $V$. Let $w$ be a real infinite place of $F$ such that every element of $V$ is smooth at $w$ (for each $g$, the function $e\mapsto \varphi(g\cdot$ `archRealLiftAt hw e` $)$ is $C^\infty$ on the invertible real $2\times2$ matrices), and let $x\in V$ be non-zero and lie in the isotypic cusp submodule `isotypicCuspSubmodule` for `pins`, $\xi$, $N$, $S$, $\Psi$, i.e. the span of the functions satisfying `IsIsotypicCuspFormAt`. The conclusion is a conjunction of two implications: first, if the function $H x - i\,(E x + F^- x)$, where each $\,\cdot\,x$ is the derivative at $t=0$ of $g\mapsto x(g\cdot$ `archFlowAt hw` $\,t)$ in the corresponding direction `ArchDir.H`, `ArchDir.E`, `ArchDir.Fm`, belongs to $V$, then it belongs to the same isotypic cusp submodule; second, if the right translate $g\mapsto x(g\cdot$ `archRealGLAt hw UpperHalfPlane.J` $)$ belongs to $V$, then it too belongs to that isotypic cusp submodule.
--
--   This is the stability statement saying that the archimedean lowering operator and right translation by the reflection $J$ at a real place preserve the $(N,S,\Psi)$-isotypic cuspidal conditions, once the resulting function is known to stay inside the constituent $V$: the level-$N$ invariance, the Hecke eigenvalue equations away from $S$ and the central character conditions are purely finite-adelic and hence commute with the archimedean flow derivatives and with the archimedean translation. It is used in the analysis of the weight-one slice of a cuspidal constituent, by [`AutomorphicForm.CuspidalConstituent.add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent`](thm.html#AutomorphicForm.CuspidalConstituent.add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent) and by [`AutomorphicForm.CuspidalConstituent.finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat`](thm.html#AutomorphicForm.CuspidalConstituent.finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem.lean

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

theorem AutomorphicForm.CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (hsm : ∀ x ∈ V, IsArchSmoothAt hw x)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hxV : x ∈ V) (hne : x ≠ 0)
    (hxiso : x ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ) :
    ((archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)) ∈ V →
      (archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x))
        ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ) ∧
    ((fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ V →
      (fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ) := by sorry
