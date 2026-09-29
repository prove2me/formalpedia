-- Prove2me | Theorems.Thm_AutomorphicForm_apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat
-- name    : AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e561b546-da57-541b-a5a0-9c0ea3916fd6
-- title:
--   Non-vanishing at s=1 of twisted GL₂ Euler products over ℚ
-- statement:
--   Fix real numbers $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and let $D=\bigcup_{x\in T}\{g x : g\in \Sigma\}$, where $\Sigma$ is the centre-cut Siegel set of parameters $(c,u,d_1,d_2)$, i.e. the set of adelic matrices whose finite component lies in the integral part, each of whose archimedean components has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$. Assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ modulo $\mathrm{GL}_2(\mathbb{Q})$ on the left and the central ideles on the right. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$, that is, a nonzero level ideal together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places, and assume the predicate `IsArithGenuineCuspRealizable` holds for $\Phi$ at the production pins attached to $D$, to the level subgroups $N\mapsto$ `levelOne` $N$ intersected with the kernel of the archimedean projection, to the Hecke generators `heckeGen`, and to the adelic box (infinite box times integral finite adeles); by definition this is the predicate `IsGenuineCuspRealizable` for the eigensystem with the same $a$ and with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$. Let $\chi:\mathbb{A}_{\mathbb{Q}}^\times\to\mathbb{C}^\times$ be a continuous homomorphism trivial on the principal ideles $\mathbb{Q}^\times$ (no unitarity is assumed), let $\varpi_v$ denote the uniformizer idele at $v$, and suppose that for some finite set $S_1$ of finite places one has $\|\chi(\varpi_v)^2 b_v\|=1$ for every $v\notin S_1$ at which the local component of $\chi$ is trivial on the units of the local integers. Then for every finite set $S$ of finite places, every $\sigma_0\in\mathbb{R}$ and every entire $\Lambda:\mathbb{C}\to\mathbb{C}$ such that for all $s$ with $\operatorname{Re} s>\sigma_0$ the family indexed by $v\notin S$ of the inverses of $P_v(N(v)^{-s})$, where $P_v(X)=1-\chi(\varpi_v)a_vX+\chi(\varpi_v)^2b_vX^2$ at unramified $v$ and $P_v=1$ otherwise and $N(v)$ is the absolute norm of $v$, has unconditional product $\Lambda(s)$, one has $\Lambda(1)\neq 0$.
--
--   This is the point $s=1$ of the Jacquet–Shalika non-vanishing theorem for the partial $L$-function of a cuspidal automorphic representation of $\mathrm{GL}_2$ over $\mathbb{Q}$ twisted by an idele class character, stated for a Hecke eigensystem realised in the cuspidal spectrum on a centre-cut Siegel covering. It is the instance over $\mathbb{Q}$ used in establishing cuspidality of the cubic automorphic induction to $\mathrm{GL}_3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat.lean

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

theorem AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Φ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 ℚ) ℚ χ) (hχc : Continuous χ)
    (S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hnorm : ∀ v ∉ S₁, IsUnramifiedCharAt χ v →
      ‖(((χ (uniformizerIdele ℚ v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v‖ = 1) :
    ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (σ₀ : ℝ) (Λ : ℂ → ℂ),
      Differentiable ℂ Λ →
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele ℚ v.1) : ℂˣ) : ℂ) * Φ.a v.1) * X
              + C ((((χ (uniformizerIdele ℚ v.1)) ^ 2 : ℂˣ) : ℂ) * Φ.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) →
      Λ 1 ≠ 0 := by sorry
