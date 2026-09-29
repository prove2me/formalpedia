-- Prove2me | Theorems.Thm_AutomorphicForm_exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable
-- name    : AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/400d58b6-105a-54b5-8a4b-3b2b5a1f7f91
-- title:
--   Entire continuation of the twisted partial L-function
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{y x : y\in \Sigma\}$, where $\Sigma$ is the centre-cut Siegel set of parameters $(c,u,d_1,d_2)$: those $g$ whose finite part is integral, whose archimedean component at each infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$. Assume `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written $\gamma g z$ inside $D$ with $\gamma\in\mathrm{GL}_2(F)$ and $z$ a central idelic scalar. Let $\Phi$ be a Hecke eigensystem over $F$ (a nonzero level ideal together with tables $a,b$ of complex numbers indexed by the finite places), and assume `IsArithGenuineCuspRealizable` for $\Phi$ relative to the carrier data `productionPinsOf` built from $D$, the level groups $\mathrm{levelOne}(N)\cap\ker(\text{archimedean part})$, the Hecke generators `heckeGen`, and the adelic box; this is the predicate `IsGenuineCuspRealizable` applied to the rescaled eigensystem $\Phi.\mathrm{toRawCentral}$, whose $b$-entries are $(\mathrm{cNorm}\,v)^{-1}b_v$. Let $\chi:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be a continuous homomorphism trivial on principal ideles (no unitarity assumed), and let $S_0$ be a finite set of finite places. Then there are a finite set $S\supseteq S_0$ of finite places, a real $\sigma_0$ and an entire $\Lambda:\mathbb{C}\to\mathbb{C}$ such that for every $s$ with $\operatorname{Re}s>\sigma_0$ the family indexed by the places $v\notin S$ of the reciprocals of $P_v(N(v)^{-s})$ is unconditionally multipliable with product $\Lambda(s)$, where $P_v(X)=1-\chi(\varpi_v)a_vX+\chi(\varpi_v)^2b_vX^2$ when $\chi$ is unramified at $v$ in the sense of `IsUnramifiedCharAt` (its local component is trivial on the units of the valuation ring), and $P_v(X)=1$ otherwise; here $\varpi_v$ is the idele `uniformizerIdele` with a uniformizer at $v$ and $N(v)$ the absolute norm of $v$.
--
--   This is the analytic continuation of the twisted partial standard $L$-function attached to the Hecke eigensystem, in the shape needed later: the Euler product over places outside a finite set converges on a right half-plane and there agrees with an entire function, the Euler polynomials being formed from the unnormalised entries $a_v,b_v$ twisted by $\chi$. It is used to rule out agreement of such eigensystems with Eisenstein tables away from a finite set, and in the cuspidality step of the Langlands–Tunnell cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable.lean

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

theorem AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S ∧ ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      Differentiable ℂ Λ ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * Φ.a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * Φ.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by sorry
