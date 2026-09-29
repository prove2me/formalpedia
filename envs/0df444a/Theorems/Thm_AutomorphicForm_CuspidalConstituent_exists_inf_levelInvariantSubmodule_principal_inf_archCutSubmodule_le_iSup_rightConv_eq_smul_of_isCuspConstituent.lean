-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/b95dfa3e-1954-568f-9f9e-195b63d93291
-- title:
--   Eigen-capture of the level-and-type cut at principal level
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, with $0<c$, $0<d_1$ and $d_1<d_2$. Write $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$ consists of those $g$ whose finite part is integral, whose archimedean components have local height at least $c$ at every infinite place, $x$-window square at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo centre, i.e. each $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\, z\in D$. Let $P$ be the production pins over $D$ with level structure $N\mapsto \mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ at the finite places, and the adelic box; its central subgroup is all of $\mathbb{A}_F^\times$, and $\xi$ is a homomorphism from it to $\mathbb{C}^\times$. Let $N\neq 0$ be an ideal, $\mathrm{tys}$ an archimedean type family (a cardinality $\mathrm{card}(w)$ and representations $\mathrm{rep}(w,i)$ at each infinite place $w$), and $V$ a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cusp constituent for $(P,\xi)$: a cusp subrepresentation, nonzero, and minimal in that every cusp subrepresentation contained in it is $0$ or $V$. Write $X=V\sqcap L\sqcap A$, where $L$ consists of the functions invariant under right translation by $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$ and $A=\mathrm{archCutSubmodule}\,F\,\mathrm{tys}$ is the intersection over infinite places $w$ of the joins over $i$ of the type submodules for $\mathrm{rep}(w,i)$; assume $X\neq 0$. Then there exist a factorizable test function $f$ (that is, $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ an archimedean test factor and $f_{\mathrm{fin}}$ a finite test factor), a natural number $n$, nonzero scalars $\lambda_i\in\mathbb{C}$ for $i\in\mathrm{Fin}\,n$, and submodules $E_i$ such that every $\varphi\in E_i$ lies in the $K$-finite cusp submodule for $(P,\xi)$ — the span of the continuous functions all of whose right translates are smooth cuspidal automorphic at the pins with central character $\xi$ and which lie in some archimedean cut submodule — and satisfies $\varphi * f=\lambda_i\varphi$ for the right convolution against $f$ with respect to the adelic $\mathrm{GL}_2$ Haar measure, and $X\le \bigsqcup_i E_i$.
--
--   This is the principal-level form of the finite eigen-capture step: the level-and-type cut of a single cuspidal constituent is swallowed by finitely many eigenspaces, with nonzero eigenvalues, of right convolution by one factorizable test function. It is cited by [`AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent`](thm.html#AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent), where the eigen-capture is converted into finite-dimensionality of the isotypic cusp spaces at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hX : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≠ ⊥) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (n : ℕ) (lam : Fin n → ℂ)
      (_ : ∀ i, lam i ≠ 0) (E : Fin n → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, ∀ φ ∈ E i, φ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧ rightConv F φ f = lam i • φ) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ ⨆ i, E i := by sorry
