-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion
-- name    : AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/00ba7a7d-dbfe-5ca7-8e1b-07cbb579ec35
-- title:
--   Integrability of a local intertwining atom and its Weyl translate
-- statement:
--   Let $F$ be a number field, $v$ a height-one prime of its ring of integers, and $F_v$ the $v$-adic completion, equipped with a Borel measurable structure compatible with its topology and an additive Haar measure $\mu$; write $\mathcal{O}_v$ for the valuation subring `adicCompletionIntegers`. Let $m \ge 1$ be a natural number and $A, B : F_v \to \mathbb{C}$ two functions subject to the local constancy hypotheses: $A(y) = A(x)$ whenever $x, y \in \mathcal{O}_v$ satisfy $v(y-x) \le \mathrm{ofAdd}(-m)$, and $B(y) = B(x)$ for all $x, y \in F_v$ with $v(y-x) \le \mathrm{ofAdd}(-m)$. Let $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$. Put $$a(x) = \mathbf{1}_{\mathcal{O}_v}(x)\,A(x) + \mathbf{1}_{F_v \setminus \mathcal{O}_v}(x)\,\mathrm{modulus}(x)^{-(2s+1)}\,B(x^{-1}),$$ where $\mathrm{modulus}(x)$ is the module of multiplication by $x$, namely $0$ for $x = 0$ and the distributive Haar character `distribHaarChar` of the unit $x$ otherwise, viewed as a nonnegative real and then as a complex number, and the exponent $-(2s+1)$ is taken in the sense of complex powers. The conclusion is the conjunction of two assertions: $a$ is $\mu$-integrable, and the function $x \mapsto \mathrm{modulus}(x)^{-(2s+1)} a(x^{-1})$ is $\mu$-integrable.
--
--   Here $a$ records the values on the big cell of a locally constant local section for $\mathrm{GL}_2$ at the finite place $v$ at parameter $s$, and the second function is its translate by the Weyl element; on $F_v$ the quantity $\mathrm{modulus}(x)$ coincides with the normalised absolute value $\lVert x \rVert$, so the two integrals are the ones occurring in the local intertwining integral. The result supplies the integrability input for the limit statements on Weyl intertwining integrals of flat families used in the analytic continuation of Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (_hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (_hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (_hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (_hs : 0 < s.re) :
    let a : v.adicCompletion F → ℂ := fun x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x
    Integrable a μ ∧
    Integrable (fun x =>
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹) μ := by sorry
