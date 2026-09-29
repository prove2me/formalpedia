-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
-- name    : AutomorphicForm.exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/05f6c78c-1f07-5872-9fae-54d86e9bc3cb
-- title:
--   Unitarity of the twisted Hecke table at almost all places
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2$ over the adele ring of $F$. Write $D=\bigcup_{x\in T}(\,\cdot\,x)\,[\,\text{centreCutSiegelSet}\ F\ c\ u\ d_1\ d_2]$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite component is integral, whose archimedean components have local height at least $c$ and $x$-window square at most $u^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_1,d_2]$ at every infinite place; assume $D$ covers $\mathrm{GL}_2$ modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,z\in D$ (here $z$ acting as the central scalar). Let $\Phi$ be a Hecke eigensystem over $F$ with values in $\mathbb{C}$, consisting of a nonzero level ideal together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places, and assume `IsArithGenuineCuspRealizable` holds for $\Phi$ relative to the production pins built from $D$, from the levels $\mathrm{levelOne}(N)\cap\ker(\text{archimedean component})$, from the Hecke generators $\mathrm{heckeGen}(v)$ and from the adelic box, i.e. `IsGenuineCuspRealizable` holds for the renormalised system $\Phi$.`toRawCentral` (same level and same $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$). Let $\chi$ be a continuous homomorphism from the idele units of $F$ to $\mathbb{C}^\times$ which is trivial on the image of $F^\times$, and let $S_1$ be a finite set of finite places such that for every $v\notin S_1$ at which $\chi$ is unramified (its local component at $v$ is trivial on the units of the local integers) one has $\lVert\chi(\varpi_v)^2 b_v\rVert=1$, where $\varpi_v$ denotes the idele $\mathrm{uniformizerIdele}\ F\ v$. Then there is a finite set $S_2$ of finite places such that for every $v\notin S_1\cup S_2$ at which $\chi$ is unramified, $$\overline{\chi(\varpi_v)a_v}=\frac{\chi(\varpi_v)a_v}{\chi(\varpi_v)^2 b_v},$$ the division being the complex quotient (so the right-hand side is $0$ when the denominator vanishes).
--
--   The conclusion expresses the self-duality, at almost every finite place, of the twisted Satake table $(\chi(\varpi_v)a_v,\ \chi(\varpi_v)^2b_v)$ attached to the cuspidal realisation of $\Phi$, the unitarity of the twisted central character being imposed by the hypothesis at places outside $S_1$. It feeds the non-vanishing at $s=1$ of the twisted Euler product in [`AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat`](thm.html#AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal Polynomial
open scoped Classical in

theorem
AutomorphicForm.exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (hnorm : ∀ v ∉ S₁, IsUnramifiedCharAt χ v →
      ‖(((χ (uniformizerIdele F v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v‖ = 1) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S₁ ∪ S₂, IsUnramifiedCharAt χ v →
      starRingEnd ℂ (((χ (uniformizerIdele F v) : ℂˣ) : ℂ) * Φ.a v) =
        (((χ (uniformizerIdele F v) : ℂˣ) : ℂ) * Φ.a v) /
          ((((χ (uniformizerIdele F v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v) := by sorry
