-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion
-- name    : AutomorphicForm.LocalIntertwining.exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/c761b36b-c6f6-5fc9-95e1-bb022f2f3938
-- title:
--   Meromorphic continuation of a local intertwining integral
-- statement:
--   Let $F$ be a number field and $v$ a nonzero prime of $\mathcal{O}_F$, and equip the completion $F_v$ with a Borel measurable structure and an additive Haar measure $\mu$. Let $\varpi \in F_v^\times$ satisfy $\mathrm{v}(\varpi) = \mathrm{ofAdd}(-1)$, i.e. $\varpi$ is a uniformiser, and let $\chi : F_v^\times \to \mathbb{C}^\times$ be a group homomorphism for which there is a $c \in \mathbb{N}$ with $\chi(u) = 1$ for every unit $u$ with $\mathrm{v}(u) = 1$ and either $c = 0$ or $\mathrm{v}(u - 1) \le \exp(-c)$. Let $m \ge 1$ be an integer, and let $A, B : \mathbb{C} \to F_v \to \mathbb{C}$ be two families with: for each $s$, $A_s$ takes equal values at any two points of $\mathcal{O}_v$ whose difference has valuation at most $\mathrm{ofAdd}(-m)$, and $B_s$ takes equal values at any two points of $F_v$ whose difference has valuation at most $\mathrm{ofAdd}(-m)$; and for each fixed $x$ the functions $s \mapsto A_s(x)$ and $s \mapsto B_s(x)$ are entire. Then there exists $M : \mathbb{C} \to \mathbb{C}$, meromorphic on all of $\mathbb{C}$, such that for every $s$ with $\|\chi(\varpi)\, N(v)^{-2s}\| < 1$ (where $N(v)$ is the absolute norm of $v$) one has $$M(s) = \int_{F_v} \Big( \mathbf{1}_{\mathcal{O}_v}(x)A_s(x) + \mathbf{1}_{F_v \setminus \mathcal{O}_v}(x)\, \chi^{-1}(x)\, |x|^{-(2s+1)}\, B_s(x^{-1}) \Big)\, d\mu(x),$$ where $\chi^{-1}(x)$ denotes the value of the inverse character extended by $0$ at $x = 0$ and $|x|$ denotes the module of $x$, i.e. the distributive Haar character of multiplication by $x$, extended by $0$ at $x = 0$.
--
--   This is the local intertwining integral attached to a level-$m$ section of a principal series of $\mathrm{GL}_2(F_v)$ at a finite place, in the form of a Tate-type local zeta integral: it converges in the half-plane where $\|\chi(\varpi)N(v)^{-2s}\| < 1$ and the function so defined continues meromorphically to the whole $s$-plane. It is the family (entire in $s$) version of the shell-by-shell evaluation [`AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion`](thm.html#AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion), and is used by [`AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_flat_family`](thm.html#AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_flat_family) to obtain meromorphic continuation of the global intertwining integral of a flat family of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.Analysis.Meromorphic.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalIntertwining.exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : ℂ → v.adicCompletion F → ℂ)
    (hA : ∀ s : ℂ, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A s y = A s x)
    (hAhol : ∀ x : v.adicCompletion F, Differentiable ℂ (fun s : ℂ => A s x))
    (B : ℂ → v.adicCompletion F → ℂ)
    (hB : ∀ s : ℂ, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B s y = B s x)
    (hBhol : ∀ y : v.adicCompletion F, Differentiable ℂ (fun s : ℂ => B s y)) :
    ∃ M : ℂ → ℂ, MeromorphicOn M Set.univ ∧
      ∀ s : ℂ, ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 →
        M s =
          ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A s) x
              + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                  (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                    * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B s y⁻¹) x) ∂μ := by sorry
