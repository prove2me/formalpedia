-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum
-- name    : AutomorphicForm.LocalIntertwining.exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/f0bfbb2f-c281-5da0-964c-f80862397f1d
-- title:
--   Polynomiality of the local intertwining integral in N(v)^{-2s}
-- statement:
--   Let $F$ be a number field, $v$ a nonzero prime of $\mathcal{O}_F$, and $F_v =$ `v.adicCompletion F` its completion, carrying a measurable structure compatible with its topology and an additive Haar measure $\mu$; write $\mathcal{O}_v$ for `v.adicCompletionIntegers F` and $q =$ `Ideal.absNorm v.asIdeal`. Let $\varpi \in F_v^\times$ satisfy $\mathrm{v}(\varpi) = \mathrm{ofAdd}(-1)$, let $\chi : F_v^\times \to \mathbb{C}^\times$ be a group homomorphism for which there is some $c \in \mathbb{N}$ with $\chi$ trivial on `higherUnitsAt F v c`, the set of units $u$ with $\mathrm{v}(u) = 1$ and, if $c \neq 0$, $\mathrm{v}(u - 1) \le \exp(-c)$. Let $m \ge 1$, let $A : F_v \to \mathbb{C}$ be $\mu$-integrable on $\mathcal{O}_v$, and let $B : F_v \to \mathbb{C}$ satisfy $B(y) = B(x)$ whenever $\mathrm{v}(y - x) \le \mathrm{ofAdd}(-m)$. Then there exist $d_0,\dots,d_m \in \mathbb{C}$, independent of $s$, such that for every $s \in \mathbb{C}$ with $\lVert \chi(\varpi)\, q^{-2s} \rVert < 1$ the function $$f_s = \mathbf{1}_{\mathcal{O}_v}\, A + \mathbf{1}_{F_v \setminus \mathcal{O}_v}\bigl(y \mapsto \mathrm{charExt}(\chi^{-1})(y)\, \mathrm{modulus}(y)^{-(2s+1)}\, B(y^{-1})\bigr)$$ is $\mu$-integrable and $(1 - \kappa\, q^{-2s}) \int_{F_v} f_s \, d\mu = \sum_{i=0}^{m} d_i\,(q^{-2s})^{i}$, where $\kappa = \chi(\varpi)$ if $\chi$ is trivial on all $u$ with $\mathrm{v}(u) = 1$ and $\kappa = 0$ otherwise. Here `charExt` $(\chi^{-1})(y)$ is $\chi(y)^{-1}$ for $y \neq 0$ and $0$ at $y = 0$, and `modulus` $(y)$ is the module of multiplication by $y$ on $(F_v,\mu)$ for $y \neq 0$ and $0$ at $y = 0$.
--
--   This is the local computation at a finite place of the intertwining integral attached to the Weyl element for a section of level $m$, written on the big cell: $A$ records the section on $\mathcal{O}_v$ and $B$ its behaviour in the opposite unipotent direction, and the conclusion says that multiplying by the inverse local Euler factor $1 - \kappa q^{-2s}$ turns the integral into a polynomial of degree at most $m$ in $q^{-2s}$. It feeds the statements on analytic continuation and growth of the normalised intertwining operators for induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Classical in

theorem AutomorphicForm.LocalIntertwining.exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    ∃ d : Fin (m + 1) → ℂ, ∀ s : ℂ,
      ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 →
        Integrable (fun x => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
              + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                  (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                    * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) μ ∧
        (1 - (if ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v 0, χ u = 1
                then ((χ ϖ : ℂˣ) : ℂ) else 0) *
              ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) *
          ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
              + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                  (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                    * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) ∂μ =
        ∑ i : Fin (m + 1), d i * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ (i : ℕ) := by sorry
