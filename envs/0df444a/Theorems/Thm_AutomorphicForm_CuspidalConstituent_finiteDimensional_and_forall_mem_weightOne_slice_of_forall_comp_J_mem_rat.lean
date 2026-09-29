-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat
-- name    : AutomorphicForm.CuspidalConstituent.finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/b5d9c83e-d6ef-5232-8c05-a39cdf44d92c
-- title:
--   Finite-dimensionality and R(J)∘ L-stability of the weight-one slice over ℚ
-- statement:
--   Work over $F=\mathbb{Q}$. Let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, and let $D=\bigcup_{x\in T}(\cdot\,x)''$ applied to the centre-cut Siegel set $\mathrm{centreCutSiegelSet}\,\mathbb{Q}\,c\,u\,d_1\,d_2$ (points with integral finite part, local height at least $c$, $x$-window at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$ at every infinite place); assume $D$ covers $\mathrm{GL}_2(\mathbb{A})$ modulo rational points and the adelic centre. Write $P$ for the production pins over $D$ with level subgroups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$, and the adelic box as conditioning set, and let $\xi$ be a character of $P.Z$ with values in $\mathbb{C}^\times$. Let $N\neq\bot$ be an ideal, $S$ a finite set of finite places, $\Psi$ a Hecke eigensystem with complex coefficients, and $V$ a cuspidal constituent for $(P,\xi)$, i.e. an irreducible cuspidal subrepresentation in the sense of `IsCuspConstituent`. Let $w$ be a real infinite place such that every $x\in V$ is archimedean-smooth at $w$ and such that $x\mapsto (g\mapsto x(g\cdot \mathrm{archRealGLAt}\,hw\,\mathrm{UpperHalfPlane.J}))$ preserves $V$. Finally let $\mathrm{tys}$ be a finite family of archimedean types which contains at $w$ both the one-dimensional types attached to the characters $\mathrm{archWeightChar}_{\mathbb{R}}(1)$ and $\mathrm{archWeightChar}_{\mathbb{R}}(-1)$, transported along the identification of $w.\mathrm{Completion}$ with $\mathbb{R}$. Put $$S_+ := V\cap \mathrm{isotypicCuspSubmodule}(P,\xi,N,S,\Psi)\cap \mathrm{archCutSubmodule}(\mathrm{tys})\cap \mathrm{archTypeSubmoduleAt}\,w\,(\text{weight }{+}1),$$ the middle factor being the span of the continuous $U(N)$-invariant smooth cuspidal automorphic forms with central character $\xi$ that are Hecke eigenfunctions with eigenvalues $\Psi.a(v)$ and central eigenvalues $\Psi.b(v)$ for $v\notin S$. Then $S_+$ is a finite-dimensional complex vector space, and for every $x\in S_+$ the function $g\mapsto \bigl(D_Hx-i(D_Ex+D_{F^-}x)\bigr)(g\cdot \mathrm{archRealGLAt}\,hw\,\mathrm{UpperHalfPlane.J})$ again lies in $S_+$, where $D_H$, $D_E$, $D_{F^-}$ are the derivatives at $t=0$ along the corresponding one-parameter archimedean flows at $w$.
--
--   This is the rational-field form of the closure statement for the weight-one slice of a cuspidal constituent: the lowering operator $L=D_H-i(D_E+D_{F^-})$ followed by right translation by $J$ at the unique real place sends the $(+1)$-weight, $\Psi$-isotypic part of $V$ back into itself, and that part is finite-dimensional. It is used in the archimedean analysis of weight-one constituents, being cited by [`AutomorphicForm.archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat`](thm.html#AutomorphicForm.archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat.lean

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

theorem AutomorphicForm.CuspidalConstituent.finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Ψ : HeckeEigensystem ℚ ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : IsCuspConstituent ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ V)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hsm : ∀ x ∈ V, IsArchSmoothAt hw x)
    (hJV : ∀ x ∈ V, (fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ V)
    (tys : ArchTypeFamily ℚ)
    (h₁ : ∃ i, tys.rep w i = ArchRepAt.ofChar ℚ ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))))
    (hm₁ : ∃ i, tys.rep w i = ArchRepAt.ofChar ℚ ((archWeightCharℝ (-1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))) :
    let Sp : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
      V ⊓ isotypicCuspSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Ψ ⊓ archCutSubmodule ℚ tys ⊓
        archTypeSubmoduleAt ℚ w (ArchRepAt.ofChar ℚ ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))))
    FiniteDimensional ℂ Sp ∧
    ∀ x ∈ Sp, (fun g => (archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)) (g * archRealGLAt hw UpperHalfPlane.J)) ∈ Sp := by sorry
