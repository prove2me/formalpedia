-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
-- name    : AutomorphicForm.exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/5978bca8-60e2-5a8b-abdf-a5fb6d044fca
-- title:
--   Uniform square-integrability of right translates on a determinant slab
-- statement:
--   Let $F$ be a number field and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the general linear group of degree $2$ over the adele ring of $F$, equipped with its Borel structure and Haar measure `adelicGLHaar`. Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_F)$, and let $D=\bigcup_{x\in T} (\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2)\,x$, where the centre-cut Siegel set consists of those $g$ whose finite part lies in the level-zero integral subgroup `finiteIntegralGL2` and whose archimedean component at every infinite place $w$ satisfies $c\le \mathrm{localHeight}$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in D$ (images taken under `globalPoints` and `centralScalar`). Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be square-integrable for the Haar measure restricted to $D$, invariant under left translation by the image of $\mathrm{GL}_2(F)$, and satisfy $f(\mathrm{centralScalar}(n)\,w)=\chi(n)f(w)$ for a nowhere-vanishing $\chi$ on the idele units. Let $0<\alpha<\beta$ and let $S$ be contained in the slab $\{g: \mathrm{ideleNorm}_F(\det g)\in[\alpha,\beta]\}$ (the norm being the module of the distinguished Haar character) and be a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the Haar measure restricted to that slab. Then for every $h$ the translate $w\mapsto f(wh)$ is square-integrable on $S$, and for all reals $0<a\le b$ there is a finite $C\in[0,\infty]$ with $\|f(\cdot\,h)\|_{L^2(S)}\le C$ for every $h$ with $\mathrm{ideleNorm}_F(\det h)\in[a,b]$.
--
--   This is the square-integrability of right translates of an automorphic function with central character, together with a bound uniform over translating elements of bounded determinant norm, on a fundamental domain cut out inside a slab of determinant norms. It is used in the construction of Rankin–Selberg test data and in the integrability statements for products of automorphic functions against powers of the idele norm of the determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (_hd : d₁ < d₂)
    (_hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ) (_hχ : ∀ n, χ n ≠ 0)
    (_hmem : MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (_hΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (_hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (α β : ℝ) (_hα : 0 < α) (_hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F)) (_hSs : S ⊆ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    (∀ h : AdelicGL2 (𝓞 F) F, MemLp (fun w => f (w * h)) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) ∧
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ h : AdelicGL2 (𝓞 F) F,
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det h) ∈ Set.Icc a b →
          eLpNorm (fun w => f (w * h)) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) ≤ C := by sorry
