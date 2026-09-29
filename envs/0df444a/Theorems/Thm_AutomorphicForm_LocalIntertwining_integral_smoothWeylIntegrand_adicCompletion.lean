-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion
-- name    : AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/8a9a6aeb-2859-5115-9861-75fd4b734f77
-- title:
--   Shell-by-shell local intertwining integral at a finite place
-- statement:
--   Let $F$ be a number field, $v$ a nonzero prime of $\mathcal O_F$, and equip the completion $F_v$ with a Borel measurable structure and an additive Haar measure $\mu$. Let $\varpi \in F_v^\times$ satisfy $v(\varpi) = \mathrm{ofAdd}(-1)$, and let $\chi : F_v^\times \to \mathbb C^\times$ be a homomorphism for which there exists $c \in \mathbb N$ with $\chi(u) = 1$ for every unit $u$ with $v(u) = 1$ and, when $c \neq 0$, $v(u-1) \le \exp(-c)$. Let $m \ge 1$, let $A : F_v \to \mathbb C$ be integrable on $\mathcal O_v$, let $B : F_v \to \mathbb C$ be constant on cosets of $\{y : v(y) \le \mathrm{ofAdd}(-m)\}$, and let $s \in \mathbb C$ satisfy $|a| < 1$ where $a = \chi(\varpi)\,q^{-2s}$ and $q = \mathrm{absNorm}(v)$. Then the $\mu$-integral over $F_v$ of $\mathbf 1_{\mathcal O_v}A + \mathbf 1_{F_v \setminus \mathcal O_v}(x)\,\chi^{-1}(x)\,\|x\|^{-(2s+1)}B(x^{-1})$, where $\chi^{-1}$ is extended by $0$ at $0$ and $\|x\|$ is the modulus of $x$ (the scaling factor of $\mu$ under multiplication by $x$, and $0$ for $x=0$), equals $$\int_{\mathcal O_v} A \,d\mu + \sum_{n=1}^{m-1}(q^{-(2s+1)})^n\int_{v(x)=\mathrm{ofAdd}(n)}\chi^{-1}(x)B(x^{-1})\,d\mu + B(0)\Big(\int_{v(u)=1}\chi^{-1}\,d\mu\Big)\frac{a^m}{1-a}.$$
--
--   This is the evaluation, at a finite place, of the intertwining integral attached to a section of a principal series that is merely smooth of level $\mathfrak p^m$ (rather than spherical) and to a possibly ramified quasi-character: the part over $\mathcal O_v$ is left as an integral, the shells $v(x)=\mathrm{ofAdd}(n)$ with $n<m$ contribute finitely many terms, and the remaining shells sum to a geometric tail. It is the computational input for the meromorphic continuation of the local factor and for the analyticity statements about the normalised intertwining operator that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion
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
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x ∂μ)
        + (∑ n ∈ Finset.Ico 1 m,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ n
              * ∫ x in {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (n : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ ∂μ)
        + B 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1}, LanglandsTunnell.TateLocal.charExt χ⁻¹ u ∂μ)
            * (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ m
            * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by sorry
