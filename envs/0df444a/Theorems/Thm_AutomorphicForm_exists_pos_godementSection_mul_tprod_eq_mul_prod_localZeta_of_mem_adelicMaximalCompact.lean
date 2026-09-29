-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
-- name    : AutomorphicForm.exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/981c7247-5fbc-56b1-b936-8c76146d9011
-- title:
--   Euler factorisation of the Godement section on the maximal compact
-- statement:
--   Let $F$ be a number field, let $\nu_0$ be a Haar measure on the idele group $(\mathbb{A}_F)^\times$, let $S$ be a finite set of finite places of $F$, let $\mu_f(v)$ and $\mu_a(w)$ be additive Haar measures on the completions at the finite places $v$ and at the infinite places $w$, and let $\varpi_v$ be a unit of $F_v$ with $v(\varpi_v)$ corresponding to $-1$, i.e. a uniformiser, for each finite $v$. Write $\alpha$ for the character of $(\mathbb{A}_F)^\times$ with values in $\mathbb{R}^\times$ obtained from the module of the distributive Haar character of $\mathbb{A}_F$, and assume $\alpha$ takes positive values (hypothesis $h\alpha$). The assertion is that there is a constant $c>0$ such that for all characters $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ with $|\mu(x)|=|\nu(x)|=1$ for all $x$, both continuous as $\mathbb{C}$-valued functions, such that $\chi=\mu\nu^{-1}$ is unramified at every $v\notin S$ (meaning that the local character $\chi_v$ obtained by restricting $\chi$ along the local unit embedding is trivial on those units $t$ with $t$ and $t^{-1}$ both integral), and for every $s$ with $\operatorname{Re}s>0$: the family $\bigl(1-\chi_v(\varpi_v)\,N(v)^{-(2s+1)}\bigr)_{v\notin S}$, with $N(v)$ the absolute norm of the prime ideal of $v$, is multipliable, its product $P(s)$ is non-zero, and for every $\Phi\colon(\mathbb{A}_F)^2\to\mathbb{C}$, every family $\Phi_{a,w}$ on $F_w^2$ and every family $\Phi_{f,v}$ on $F_v^2$ such that $\Phi(x)=0$ whenever some coordinate $x_i$ has non-integral component at some $v\notin S$ and $\Phi(x)=\bigl(\prod_w\Phi_{a,w}(x_w)\bigr)\prod_{v\in S}\Phi_{f,v}(x_v)$ whenever all components of all $x_i$ at places outside $S$ are integral, and for every $k$ in the adelic maximal compact subgroup (finite part in $\mathrm{finiteIntegralGL2}$, each archimedean component a row isometry), one has $$\mathrm{godementSection}(F,\nu_0,\mu,\nu,\alpha,h\alpha,\Phi,s,k)\cdot P(s)=c\,\mu(\det k)\prod_w Z_w\prod_{v\in S}Z_v,$$ where $\mathrm{godementSection}$ is $\mu(\det k)\,\alpha(\det k)^{s+1/2}$ times the global Tate zeta integral of $t\mapsto\Phi(t\cdot(\text{second row of }k))$ against $\chi$ at $2s+1$, and $Z_w$, $Z_v$ are Tate's local zeta integrals at $2s+1$ of $t\mapsto\Phi_{a,w}(t\cdot(\text{second row of }k_w))$, resp. $t\mapsto\Phi_{f,v}(t\cdot(\text{second row of }k_v))$, against the local characters of $\chi$ at $w$, resp. $v$.
--
--   This is the restricted-tensor-product factorisation of Godement's section of a factorisable function of two variables, evaluated on the standard maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$: the global zeta integral becomes a product of Tate local zeta integrals at the places in $S$ and at infinity, the unramified places outside $S$ contributing the inverse of the partial Euler product $P(s)$. It is cited by [`AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family`](thm.html#AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family), and rests on the corresponding factorisation of the global zeta integral, [`NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq`](thm.html#NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
        (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
        (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
        (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
        (_hS : ∀ v ∉ S, IsUnramifiedCharAt (μ * ν⁻¹) v)
        (s : ℂ) (_hs : 0 < s.re),
        Multipliable (fun v : {v // v ∉ S} =>
            1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ∧
        (∏' v : {v // v ∉ S},
            (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ≠ 0 ∧
        ∀ (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
          (Φa : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
          (Φf : (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ)
          (_hΦ0 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∃ v ∉ S, ∃ i, (x i).2 v ∉ v.adicCompletionIntegers F) → Φ x = 0)
          (_hΦ1 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∀ v ∉ S, ∀ i, (x i).2 v ∈ v.adicCompletionIntegers F) →
              Φ x = (∏ w, Φa w (fun i => (x i).1 w)) * ∏ v ∈ S, Φf v (fun i => (x i).2 v))
          (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F),
          godementSection F ν₀ μ ν α hα Φ s k
              * ∏' v : {v // v ∉ S},
                  (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
            = c * ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                    (fun t => Φa w (fun i => t
                      * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                    (archLocalChar (μ * ν⁻¹) w) (2 * s + 1))
                * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf v (fun i => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i))
                    (localChar (μ * ν⁻¹) v) (2 * s + 1) := by sorry
