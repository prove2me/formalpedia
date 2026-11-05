-- Prove2me | Theorems.Thm_BauerleRiederMDP_TransactionCosts_proposition_4_5_2
-- name    : BauerleRiederMDP.TransactionCosts.proposition_4_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:22.368139+00:00
-- url     : https://prove2.me/theorems/a41ba4b5-9a06-4cf6-9d50-19896ad308cd
-- title:
--   Proposition 4.5.2 (corrected: $\mathbb M$ restricted to upper semicontinuous functions) — (SA$_N$) with buy/hold/sell maximizers
-- statement:
--   Consider the terminal wealth problem with proportional transaction costs of §4.5 under its standing assumptions, with $\mathbb M$ the set of increasing, concave, $\gamma$-homogeneous functions in $\mathbb B^+_b$, $b(x)=1+x_0+x_1$, and $\Delta$ the set (4.26) of buy/hold/sell rules. Let $\mathbb M^{usc}$ be the set of $v\in\mathbb M$ that are upper semicontinuous on $E$. Then the Structure Assumption (SA$_N$) holds with $\mathbb M_n:=\mathbb M^{usc}$ and $\Delta_n:=\Delta\cap F_n$:
--
--   1. $g_N(x)=U(x_0+x_1)$ belongs to $\mathbb M^{usc}$;
--   2. for every $n<N$ and $v\in\mathbb M^{usc}$, the operator $T_nv$ is well defined, i.e. for every $x\in E$ and $(a_0,a_1)\in D(x)$ the expectation $\mathbb E\,v(a_0(1+i_{n+1}),a_1\tilde R_{n+1})$ exists, and $T_nv\in\mathbb M^{usc}$;
--   3. for every $n<N$ and $v\in\mathbb M^{usc}$ there is $f\in\Delta$ such that $x\mapsto(h(x,f(x)),f(x))$ is a decision rule and is a maximizer of $v$ at time $n$:
--   $$\mathbb E\,v\big(h(x,f(x))(1+i_{n+1}),\ f(x)\tilde R_{n+1}\big)=T_nv(x)\qquad\text{for all }x\in E.$$
--
--   By the Structure Theorem 2.3.8 this yields the existence of optimal policies of buy/hold/sell form, made explicit in Theorem 4.5.4.
--
--   **Why the correction.** With $\mathbb M_n:=\mathbb M$ as printed, part 3 fails. Take $c=\frac12$, $U(x)=\sqrt x$ ($\gamma=\frac12$), $N=1$, $i_1=0$, $\tilde R_1\equiv1$, and $v(x_0,x_1)=\sqrt{x_0+x_1}$ for $x_1>0$, $v(x_0,0)=\frac12\sqrt{x_0}$. This $v$ is measurable, increasing, concave, homogeneous of degree $\frac12$ and $v\le b$, so $v\in\mathbb M$. At $x=(1,0)$, $D(x)=\{a_0+\frac32a_1\le1\}$ and $T_0v(1,0)=\sup_{D(x)}v=1$, which is not attained: $v(a)<1$ for $a_1>0$ and $v(a)\le\frac12$ for $a_1=0$. The proof's step (ii) assumes that a concave function on $[0,1]$ has a maximum point, which needs upper semicontinuity; $T_n$ preserves upper semicontinuity, as in the semicontinuous models of §2.4.1.
--
--   **Formalization Note** The stock-only maximizer $f\in\Delta$ is identified with the decision rule $(h(x,f(x)),f(x))$, as the book does on p.108 ("it is enough to determine the amount invested in the stock after transaction").
--
--   Differences from the source:
--   - correction: 𝕄_n := 𝕄 (increasing, concave, γ-homogeneous functions in 𝔹_b^+) → 𝕄_n := 𝕄 ∩ {v upper semicontinuous on E}, in hypotheses and conclusions; reason: as printed (iii) is false: c = 1/2, U = √x, γ = 1/2, N = 1, i_1 = 0, R̃_1 ≡ 1, v = √(x₀+x₁) for x₁ > 0 and v(x₀,0) = √x₀/2 is in 𝕄, and T_0 v(1,0) = 1 is not attained on D(1,0)
--   - reading: f₊(x₀,x₁) < x₁, f₋(x₀,x₁) > x₁ and the three cases of (4.26), x₁/x₀ undefined at x = 0 → inequalities on the regions where f = f₊, resp. f = f₋; region conditions at every x ∈ E with x ≠ (0,0); reason: f₊ ≥ 0 makes f₊ < x₁ impossible at x₁ = 0, so the inequalities can only hold on the regions; at (0,0) the ratio is undefined and D(0,0) = {(0,0)} fixes f(0,0) = 0
--   - reading: maximizer f_n ∈ Δ_n = Δ ∩ F_n with Δ a set of functions E → ℝ₊ → f ∈ Δ such that x ↦ (h(x, f(x)), f(x)) is a decision rule and a maximizer; reason: p.108: the decision rule is determined by its stock component, with bond amount h(x, a)
--   - encoding: T_n v well-defined → for all x ∈ E, a ∈ D(x): IE v⁺ < ∞ or IE v⁻ < ∞ for v(a₀(1+i_{n+1}), a₁R̃_{n+1}); reason: the expectation exists exactly in this case (Definition 2.3.1: whenever the integral exists)
--   - encoding: functions E → [−∞, ∞) and their expectations → EReal-valued functions; expectation IE f⁺ − IE f⁻ in EReal (eexp); reason: Lean convention; same instances, and every expectation used exists
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 4.5.2, p.109 (PDF 123); Structure Assumption (SA_N), p.23 (PDF 38); Definition 2.3.6, p.21 (PDF 36)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Assumptions
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
import Definitions.Def_BauerleRiederMDP_TransactionCosts_admissibleSet
import Definitions.Def_BauerleRiederMDP_TransactionCosts_bondAfter
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_transition
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Lop
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Top
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IsDecisionRule
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IM
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IsConeRule

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.TransactionCosts

/-- Proposition 4.5.2 of Bäuerle & Rieder (2011), *Markov Decision Processes with Applications
to Finance*, p.109 (PDF 123), **corrected**: the Structure Assumption (SA_N) (p.23, PDF 38) holds
for the terminal wealth problem with transaction costs with `IM_n := IM ∩ {v upper
semicontinuous on E}` and `Δ_n := Δ ∩ F_n`, where `Δ` is the set (4.26) of cone-shaped
buy/hold/sell rules:

(i) `g_N(x) = U(x₀ + x₁)` is in `IM` and upper semicontinuous on `E`;
(ii) for `v` in `IM` and upper semicontinuous on `E`, `T_n v` is well-defined (for every `x ∈ E`
and `a ∈ D(x)` the expectation `IE v(a₀(1 + i_{n+1}), a₁R̃_{n+1})` exists, i.e. `IE v⁺ < ∞` or
`IE v⁻ < ∞`) and `T_n v` is again in `IM` and upper semicontinuous on `E`;
(iii) for such `v` there is a maximizer of `v` at time `n` in `Δ_n`: a function `f ∈ Δ` (the
stock amount after transaction) such that `x ↦ (h(x, f(x)), f(x))` is a decision rule and
`L_n v(x, (h(x, f(x)), f(x))) = T_n v(x)` for every `x ∈ E` (Definition 2.3.6, p.21).

**Correction.** As printed (`IM_n := IM`), (iii) is false: with `c = 1/2`, `U(x) = √x`
(`γ = 1/2`), `N = 1`, `i_1 = 0`, `R̃_1 ≡ 1`, the function `v(x₀, x₁) = √(x₀ + x₁)` for `x₁ > 0`,
`v(x₀, 0) = √x₀ / 2` is measurable, increasing, concave, homogeneous of degree `1/2` and
`v ≤ b`, so `v ∈ IM`; at `x = (1, 0)` one has `L_0 v(x, (a₀, a₁)) = v(a₀, a₁)`,
`D(x) = {a₀ + (3/2)a₁ ≤ 1}`, and `T_0 v(1, 0) = 1` is not attained (`< 1` for `a₁ > 0`, `≤ 1/2`
for `a₁ = 0`). The proof's step (ii) ("a concave function on the compact interval [0, 1]" has a
maximum point) needs upper semicontinuity, which `T_n` preserves (Section 2.4.1).

**Formalization Note.** Functions on `E` are `EReal`-valued (the book's `[−∞, ∞)`), the
expectation is `eexp`, and the stock-only maximizer `f ∈ Δ` is identified with the decision rule
`(h(x, f(x)), f(x))` (p.108: "it is enough to determine the amount invested in the stock after
transaction"). -/
theorem proposition_4_5_2 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) :
    (IM M.γ (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) ∧
      UpperSemicontinuousOn (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) stateSpace) ∧
    ∀ n < M.N, ∀ v : ℝ × ℝ → EReal, IM M.γ v → UpperSemicontinuousOn v stateSpace →
      (∀ x ∈ stateSpace, ∀ a ∈ admissibleSet M.c x,
        (∫⁻ ω, (v (M.transition n a (M.R (n + 1) ω))).toENNReal ∂M.P) < ⊤ ∨
        (∫⁻ ω, (-v (M.transition n a (M.R (n + 1) ω))).toENNReal ∂M.P) < ⊤) ∧
      (IM M.γ (M.Top n v) ∧ UpperSemicontinuousOn (M.Top n v) stateSpace) ∧
      ∃ f : ℝ × ℝ → ℝ, IsConeRule f ∧
        IsDecisionRule M.c (fun x => (bondAfter M.c x (f x), f x)) ∧
        ∀ x ∈ stateSpace, M.Lop n v x (bondAfter M.c x (f x), f x) = M.Top n v x := by sorry

end BauerleRiederMDP.TransactionCosts
