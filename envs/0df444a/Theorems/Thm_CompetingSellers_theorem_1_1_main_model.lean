-- Prove2me | Theorems.Thm_CompetingSellers_theorem_1_1_main_model
-- name    : CompetingSellers.theorem_1_1_main_model
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:46.42268+00:00
-- url     : https://prove2.me/theorems/6008b8b3-e78d-4ffa-8e1e-e823e92dcd1f
-- title:
--   Theorem 1.1 (Main Model) — Alice's optimal Stackelberg revenue beats Bertrand iff $a<C\,b$; all optimal mechanisms characterized
-- statement:
--   Let $\Sigma$ be an uncountable standard Borel message space with a null message, and let the buyer's values be $a,b>0$. Then:
--
--   1. there is a $C\in(3.146,3.147)$ with $C-\ln C=2$, and an Alice-optimal mechanism exists;
--   2. for every $C>1$ with $C-\ln C=2$: $C\in(3.146,3.147)$; a mechanism is Alice-optimal iff it satisfies the condition of Proposition 3.20; and
--   $$\mathrm{opt}_A(a;b)>(a-b)^+\iff a<C\,b,\qquad \mathrm{opt}_A(a;b)=(a-b)^+\ \text{ if } a\ge C\,b;$$
--   3. the equilibrium payoffs (Alice's revenue, Bob's revenue, the buyer's utility) are the same in every Stackelberg equilibrium;
--   4. there is a lottery $E=(x_E,\tau_E)$ such that for every Alice-optimal $A$ and every mechanism $B$ posting the price $b$ (realizing $\mathrm{FP}(b)$, which exists): $B$ is a best response of Bob to $A$, and every selected buyer plan visits Alice first, takes from her an option with allocation $x_E$ and expected payment $\tau_E$, then gets nothing from Bob after winning Alice's good (if $x_E>0$) and buys Bob's good after losing it (if $x_E<1$);
--   5. if $a<C\,b$, there are $x_B<x_E$ and $\varphi$ with $\varphi(x_E)=\tau_E$ such that every Alice-optimal mechanism offers the options $(x,\varphi(x))$ for all $x\in[x_B,x_E]$, and no Alice-optimal mechanism has a finite menu.
--
--   Alice, the incumbent, commits to an arbitrary randomized mechanism; Bob answers; the buyer chooses the order of visits. With posted prices only she would earn her Bertrand revenue $(a-b)^+$; with lotteries she earns strictly more exactly when $a<Cb$, and then only menus with a continuum of options are optimal.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - reading: "There exists a complete and explicit characterization of all mechanisms that are Alice-optimal … (Proposition 3.20), and it defines the optimal revenue for Alice" → an Alice-optimal mechanism exists, and IsAliceOptimal ↔ Prop320Condition; reason: footnote 17: the final result rules out an unattained supremum; Proposition 3.20 is the characterization
--   - reading: "posting a price of b is a best response … it is optimal for the buyer to visit Alice first, select a specific lottery from her (point E) and buy from Bob if and only if he got nothing" → ∃ (x_E, τ_E) such that for every optimal A and every mechanism realizing FP(b): best response, selected plans exist, visit Alice first, take an option (x_E, τ_E), Bob allocation 0 on the win branch if x_E > 0 and 1 on the lose branch if x_E < 1; reason: "buy from Bob iff" is stated on branches of positive probability (Definition 2.1); E is the same lottery for all optimal mechanisms
--   - reading: "all these mechanisms share an infinite continuum of menu options ending at the lottery selected by the buyer (point E)" → ∃ x_B < x_E and φ with φ(x_E) = τ_E such that every optimal mechanism offers every option (x, φ(x)), x ∈ [x_B, x_E], and no optimal mechanism has a finite menu; reason: footnote 6: "requiring infinitely many menu options means that no finite menu attains Alice's exact optimum"
--   - encoding: "where C ∈ (3.146, 3.147) satisfies C − ln C = 2" → ∃ C in the interval with C − log C = 2, and every C > 1 with C − log C = 2 lies in the interval; reason: C − ln C = 2 has a second root in (0, 1), excluded by C > 1; same instances
--   - encoding: Bertrand revenue (a − b)⁺ → max (a − b) 0; reason: notation
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Theorem 1.1, p.2 (PDF 5); restated p.18 (PDF 21); footnotes 3, 6, 17

import Mathlib
import Definitions.Def_CompetingSellers_optA
import Definitions.Def_CompetingSellers_Prop320Condition

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Theorem 1.1 (Main Model).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Theorem 1.1, p.2 (PDF 5; restated p.18, PDF 21): "Consider an instance of the duopoly game
in the main model with fixed buyer values `a, b > 0`. There exists a complete and explicit
characterization of all mechanisms that are Alice-optimal in a Stackelberg equilibrium
(Proposition 3.20), and it defines the optimal revenue for Alice. The equilibrium utilities of
all three agents (Alice, Bob and the buyer) are independent of the equilibrium selection. For each
Alice-optimal mechanism, posting a price of `b` is a best response for Bob. Under this response,
it is optimal for the buyer to visit Alice first, select a specific lottery from her (point E in
Figure 1), and buy from Bob if and only if he got nothing from Alice's lottery. Alice's optimal
revenue strictly exceeds her Bertrand revenue `(a − b)⁺` if `a < C · b`, and equals it otherwise,
where `C ∈ (3.146, 3.147)` satisfies `C − ln C = 2`. When `a < C · b`, all these mechanisms share
an infinite continuum of menu options ending at the lottery selected by the buyer (point E)."

**Formalization Note.** The message space `Σ` is quantified: the theorem is stated for every
uncountable standard Borel `S` with a null message. "Complete characterization … defines the
optimal revenue" is read as: an Alice-optimal mechanism exists (the supremum `optA` is attained,
footnote 17) and Proposition 3.20's condition characterizes them. Point E is the lottery
`(x_E, τ_E)` (allocation probability, expected payment). "Posting a price of `b`" is any mechanism
realizing `FP(b)`; "buy from Bob iff he got nothing" is stated on the branches reached with
positive probability (Definition 2.1). The "infinite continuum" is read through footnote 6
("no finite menu attains Alice's exact optimum") together with a common family of options
`(x, φ(x))`, `x ∈ [x_B, x_E]`, `x_B < x_E`, offered by every optimal mechanism and ending at E. -/
theorem theorem_1_1_main_model (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃ C : ℝ, 3.146 < C ∧ C < 3.147 ∧ C - Real.log C = 2) ∧
    (∃ A : Mech S null, IsAliceOptimal a b A) ∧
    (∀ C : ℝ, 1 < C → C - Real.log C = 2 →
      (3.146 < C ∧ C < 3.147) ∧
      (∀ A : Mech S null, IsAliceOptimal a b A ↔ Prop320Condition a b C A) ∧
      (max (a - b) 0 < optA S null a b ↔ a < C * b) ∧
      (C * b ≤ a → optA S null a b = max (a - b) 0)) ∧
    (∀ (A A' : Mech S null) (𝓜 𝓜' : Mech S null → Mech S null),
      IsStackelbergEq a b A 𝓜 → IsStackelbergEq a b A' 𝓜' →
        eqPayoffs a b A (𝓜 A) = eqPayoffs a b A' (𝓜' A')) ∧
    (∃ B : Mech S null, IsPricingMech (fp b) B) ∧
    ∃ xE τE : ℝ,
      (∀ A : Mech S null, IsAliceOptimal a b A →
        ∀ B : Mech S null, IsPricingMech (fp b) B →
          IsBestResponse a b A B ∧ (selectedPlans a b A B).Nonempty ∧
          ∀ π ∈ selectedPlans a b A B, π.first = Seller.alice ∧ A.alloc π.msg1 = xE ∧
            A.pay π.msg1 = ENNReal.ofReal τE ∧ (0 < xE → B.alloc π.msgW = 0) ∧
            (xE < 1 → B.alloc π.msgL = 1)) ∧
      ∀ C : ℝ, 1 < C → C - Real.log C = 2 → a < C * b →
        (∃ (xB : ℝ) (φ : ℝ → ℝ), xB < xE ∧ φ xE = τE ∧
          ∀ A : Mech S null, IsAliceOptimal a b A → ∀ x ∈ Set.Icc xB xE,
            ∃ σ : S, A.alloc σ = x ∧ A.pay σ = ENNReal.ofReal (φ x)) ∧
        ∀ A : Mech S null, IsAliceOptimal a b A → ¬ A.FiniteMenu := by sorry

end CompetingSellers
