-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
-- name    : AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6ba58e02-ea7e-5882-9027-4798c7d94d67
-- title:
--   Right convolution preserves the isotypic cusp space
-- statement:
--   Work over $F=\mathbb{Q}$. Let $c,u,d_1,d_2$ be real numbers and $T$ a finite set of elements of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, and set $D=\bigcup_{x\in T}\,(\cdot\,x)$-translates of `centreCutSiegelSet ℚ c u d₁ d₂`, the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component has local height at least $c$ and window square at most $u^2$ at every infinite place, and whose archimedean determinant norm lies in $[d_1,d_2]$ at every infinite place. Assume $d_1<d_2$ and that $D$ covers modulo the centre, i.e. for each adelic $g$ there are $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and an idele unit $z$ with $\gamma g\,z\in D$. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$ (a nonzero level ideal $\Phi.\mathrm{level}$ and families $\Phi.a,\Phi.b$ indexed by the finite places), and let `pins` be the carrier data `productionPinsOf` attached to $D$, to the level groups $N\mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, to the Hecke generators $v\mapsto$ `heckeGen (𝓞 ℚ) ℚ v`, and to the measure conditioned on `adelicBox ℚ`. Let $R$ be a smooth cuspidal realization at `pins` of the renormalised eigensystem `Φ.toRawCentral` (same level and same $\Phi.a$, with central eigenvalues $(\mathrm{cNorm}\,v)^{-1}\Phi.b(v)$), with $R.\mathrm{toFun}$ continuous. Let $f$ be a factorizable test function on adelic $\mathrm{GL}_2$, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for an archimedean and a finite test factor, and assume every $x$ with $f(x)\neq 0$ factors as $x=ak$ with $\mathrm{glFin}\,a=1$ and $k\in$ `levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ`. Then the right convolution $g\mapsto\int R.\mathrm{toFun}(gx)f(x)\,d\mu(x)$ against the adelic $\mathrm{GL}_2$ Haar measure is an isotypic cusp form at `pins` for the central character $R.\mathrm{centralChar}$, the level $\Phi.\mathrm{level}$, the exceptional set $R.\mathrm{exceptionalSet}$ and the eigensystem $\Phi$: it is a smooth cuspidal automorphic function at `pins` for $R.\mathrm{centralChar}$, continuous, right invariant under `levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ`, a Hecke coset eigenfunction at `heckeGen (𝓞 ℚ) ℚ v` with eigenvalue $\Phi.a(v)$ for every $v$ outside $R.\mathrm{exceptionalSet}$, and satisfies $\varphi(\mathrm{centralScalar}(\det(\mathrm{heckeGen}\,v))\,g)=(\mathrm{cNorm}\,v)^{-1}\Phi.b(v)\,\varphi(g)$ for all such $v$ and all $g$.
--
--   This is the stability of the isotypic cusp space under right convolution by a factorizable test function supported in the level group: smoothing a continuous cuspidal realization of a Hecke eigensystem neither destroys cuspidality and level invariance nor changes the Hecke and central eigenvalues. It is used to produce enough smooth vectors inside the isotypic space for the representation-theoretic steps of the converse direction — irreducibility of the span of translates of a realization, and the archimedean Casimir and Whittaker computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (hfs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv ℚ R.toFun f) := by sorry
