-- Prove2me | Theorems.Thm_CompetingSellers_Supplement_theorem_1_3_aligned_model
-- name    : CompetingSellers.Supplement.theorem_1_3_aligned_model
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:33:28.652506+00:00
-- url     : https://prove2.me/theorems/4630fa9c-6612-49f8-9f1c-15b6225e7d27
-- title:
--   Theorem 1.3 (Aligned Model) — $\mathrm{opt}^{AB}_A=a-b+be^{-a/b}$ ($a\ge b$), $a^2/(eb)$ ($a<b$), always above Bertrand; optimal mechanisms characterized
-- statement:
--   Let $\Sigma$ be an uncountable standard Borel message space with a null message and let $a,b>0$. In the **aligned model** Alice commits to a mechanism, Bob responds, and the buyer must visit Alice first. Write $\mathrm{opt}^{AB}_A(a;b)$ for Alice's optimal revenue over the Stackelberg equilibria of this model and $x_{eq}$ for $\frac ab(1-\frac1e)$ if $a<b$ and $1-e^{-a/b}$ if $a\ge b$. Then:
--
--   1. an Alice-optimal mechanism exists, and a mechanism $A$ is Alice-optimal if and only if it satisfies the condition of Proposition 4.9; moreover every $t\in[x_{eq},1]$ is the largest maximizer $z^+_A(a)$ of some Alice-optimal $A$;
--   2. Alice's optimal revenue is
--   $$\mathrm{opt}^{AB}_A(a;b)=\begin{cases}a-b+b\,e^{-a/b},&a\ge b,\\[2pt] \dfrac{a^2}{e\,b},&a<b,\end{cases}$$
--   and it strictly exceeds her Bertrand revenue $(a-b)^+$ for all $a,b>0$;
--   3. the payoff triple (Alice's revenue, Bob's revenue, the buyer's utility) is the same in every Stackelberg equilibrium;
--   4. there is a lottery $E'=(x_E,\tau_E)$ (allocation probability, expected payment), and there are $x_{lo}<x_E$ and $\varphi$ with $\varphi(x_E)=\tau_E$, such that every Alice-optimal mechanism offers the options $(x,\varphi(x))$ for all $x\in[x_{lo},x_E]$; for every Alice-optimal $A$ and every mechanism $B$ posting the price $b$ (such $B$ exist), $B$ is a best response of Bob, and every selected buyer plan takes from Alice an option with allocation $x_E$ and expected payment $\tau_E$, then gets nothing from Bob after winning Alice's good (if $x_E>0$) and buys Bob's good after losing it (if $x_E<1$);
--   5. no Alice-optimal mechanism has a finite menu.
--
--   Unlike the main model (Theorem 1.1), commitment and randomization give Alice strictly more than her Bertrand revenue for every $a,b>0$ when the buyer must visit her first.
--
--   **Formalization Note** All revenues, buyer plans and utilities are the fixed-order ones with Alice first (`revenueFrom`, `selectedPlansFrom`, `orderUtil … alice`). The readings of "characterization", "shared continuum" and "buy from Bob iff he got nothing" are those of the published Theorem 1.1.
--
--   Differences from the source:
--
--   - reading: a complete and explicit characterization (Proposition 4.9), which defines the optimal revenue → an Alice-optimal mechanism exists, and A is Alice-optimal iff it satisfies Proposition 4.9's condition; reason: the same reading as the published Theorem 1.1; existence is what makes the characterization define the optimum
--   - reading: Proposition 4.9: the largest maximizer z⁺_A(a) may be any value in [z⁻_A(a), 1] → every t ∈ [x_eq, 1] equals z⁺_A(a) for some Alice-optimal A; reason: the sentence is part of the cited characterization; read as attainment of every value
--   - reading: all optimal mechanisms share an infinite continuum of menu options with E′ at its top → there are x_lo < x_E and φ with φ(x_E) = τ_E such that every Alice-optimal A offers (x, φ(x)) for all x ∈ [x_lo, x_E]; and no Alice-optimal A has a finite menu; reason: the same reading as the published Theorem 1.1, with footnote 6 ("no finite menu attains Alice's exact optimum")
--   - reading: buy from Bob if and only if he got nothing from Alice's lottery → Bob's allocation is 0 after winning Alice's good (if x_E > 0) and 1 after losing it (if x_E < 1), for every selected plan; reason: only branches reached with positive probability are constrained (Definition 2.1), as in the published Theorem 1.1
--   - encoding: posting a price of b → any mechanism realizing FP(b) (IsPricingMech (fp b) B), and one exists; reason: Bob's strategies are general mechanisms; all realizations of FP(b) have the same menu
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Theorem 1.3, p.31 (PDF 34); first stated p.5 (PDF 8); Proposition 4.9, p.38 (PDF 41); footnote 6, p.4 (PDF 7)

import Mathlib
import Definitions.Def_CompetingSellers_Supplement_IsStackelbergEqFrom
import Definitions.Def_CompetingSellers_Supplement_Prop49Condition
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers.Supplement

/-- **Theorem 1.3 (Aligned Model).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Theorem 1.3, p.31 (PDF 34; first stated p.5, PDF 8): "Consider an
instance of the duopoly game in the aligned model with fixed buyer values `a, b > 0`. There exists
a complete and explicit characterization of all mechanisms that are Alice-optimal in a Stackelberg
equilibrium (Proposition 4.9), and it defines the optimal revenue for Alice:
`opt^{AB}_A(a; b) = a − b + b·e^{−a/b}` for `a ≥ b`, `a²/(e·b)` for `a < b`, which strictly
exceeds her Bertrand revenue of `(a − b)⁺`, for all `a, b > 0`. The equilibrium utilities of all
three agents (Alice, Bob and the buyer) are independent of the equilibrium selection. All the
mechanisms Alice offers in these equilibria share an infinite continuum of menu options; posting a
price of `b` is a best response for Bob and under this response, it is optimal for the buyer to
select the lottery at the top of this shared continuum (point E′ in Figure 4) and buy from Bob if
and only if he got nothing from Alice's lottery."

**Formalization Note.** The aligned model is the fixed-order model with first seller `alice`
(`revenueFrom`, `selectedPlansFrom`, `orderUtil … alice`). `Σ` is quantified as in Theorem 1.1.
"Complete characterization … defines the optimal revenue" is read as: an Alice-optimal mechanism
exists and Proposition 4.9's condition characterizes them; Proposition 4.9's last sentence
("`z⁺_A(a)` may be any value in `[z⁻_A(a), 1]`") is the clause that every value in
`[x_eq, 1]` is attained by some optimal mechanism. Point E′ is the lottery `(x_E, τ_E)`
(allocation probability, expected payment); "posting a price of `b`" is any mechanism realizing
`FP(b)`; "buy from Bob iff he got nothing" is stated on the branches reached with positive
probability. The "infinite continuum" is read as in Theorem 1.1: a common family of options
`(x, φ(x))`, `x ∈ [x_lo, x_E]`, `x_lo < x_E`, offered by every optimal mechanism and ending at E′,
together with footnote 6 ("no finite menu attains Alice's exact optimum"). -/
theorem theorem_1_3_aligned_model (S : Type) [MeasurableSpace S] [StandardBorelSpace S]
    [Uncountable S] (null : S) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃ A : Mech S null, IsAliceOptimalFrom a b Seller.alice A) ∧
    (∀ A : Mech S null, IsAliceOptimalFrom a b Seller.alice A ↔ Prop49Condition a b A) ∧
    (∀ t ∈ Set.Icc (xeqAligned a b) 1, ∃ A : Mech S null,
      IsAliceOptimalFrom a b Seller.alice A ∧ mZPlus a A a = t) ∧
    (b ≤ a → optAFrom S null a b Seller.alice = a - b + b * Real.exp (-(a / b))) ∧
    (a < b → optAFrom S null a b Seller.alice = a ^ 2 / (Real.exp 1 * b)) ∧
    max (a - b) 0 < optAFrom S null a b Seller.alice ∧
    (∀ (A A' : Mech S null) (𝓜 𝓜' : Mech S null → Mech S null),
      IsStackelbergEqFrom a b Seller.alice A 𝓜 → IsStackelbergEqFrom a b Seller.alice A' 𝓜' →
        eqPayoffsFrom a b Seller.alice A (𝓜 A) = eqPayoffsFrom a b Seller.alice A' (𝓜' A')) ∧
    (∃ B : Mech S null, IsPricingMech (fp b) B) ∧
    ∃ xE τE : ℝ,
      (∃ (xlo : ℝ) (φ : ℝ → ℝ), xlo < xE ∧ φ xE = τE ∧
        ∀ A : Mech S null, IsAliceOptimalFrom a b Seller.alice A → ∀ x ∈ Set.Icc xlo xE,
          ∃ σ : S, A.alloc σ = x ∧ A.pay σ = ENNReal.ofReal (φ x)) ∧
      (∀ A : Mech S null, IsAliceOptimalFrom a b Seller.alice A →
        ∀ B : Mech S null, IsPricingMech (fp b) B →
          IsBestResponseFrom a b Seller.alice A B ∧
          (selectedPlansFrom a b Seller.alice A B).Nonempty ∧
          ∀ π ∈ selectedPlansFrom a b Seller.alice A B, A.alloc π.msg1 = xE ∧
            A.pay π.msg1 = ENNReal.ofReal τE ∧ (0 < xE → B.alloc π.msgW = 0) ∧
            (xE < 1 → B.alloc π.msgL = 1)) ∧
      ∀ A : Mech S null, IsAliceOptimalFrom a b Seller.alice A → ¬ A.FiniteMenu := by sorry

end CompetingSellers.Supplement
