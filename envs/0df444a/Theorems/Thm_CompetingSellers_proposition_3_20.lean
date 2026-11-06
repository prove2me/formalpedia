-- Prove2me | Theorems.Thm_CompetingSellers_proposition_3_20
-- name    : CompetingSellers.proposition_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:51.820454+00:00
-- url     : https://prove2.me/theorems/88c6c132-5394-4af9-8302-f05b84843cd2
-- title:
--   Proposition 3.20 — characterization of all Alice-optimal mechanisms
-- statement:
--   Let $\Sigma$ be an uncountable standard Borel message space with null message, $a,b>0$, $\Delta=|a-b|$, and $C\in(3.146,3.147)$ with $C-\ln C=2$. A mechanism $A$ is optimal for Alice if and only if:
--
--   1. when $a<b$: $z^+_A$ is monotone, $\mathrm{util}_A=\mathrm{util}_{A^*_{LB}}$ on $[s^*,a]$ and $z^+_A(v)\in\big[\frac{v-R^*_{LB}+\Delta}{v+\alpha^*(v-\mathrm{util}_A(v))},\frac{\mathrm{util}_{A^*_{LB}}(a)}b\big]$ on $(0,s^*]$;
--   2. when $b\le a<Cb$: $z^+_A$ is monotone, $\mathrm{util}_A=\mathrm{util}_{A^*_{LA}}$ on $\{\Delta\}\cup[s^*,a]$ and $z^+_A(v)\in\big[1-\frac{R^*_{LA}}{v-\Delta},\frac{\mathrm{util}_{A^*_{LA}}(a)}b\big]$ on $(\Delta,s^*]$;
--   3. when $Cb\le a$: $A$ is a posted price of $a-b$;
--
--   with the optimal equalizers $A^*_{LB},A^*_{LA}$ of Definition 3.19 and $u^*,\alpha^*,s^*$ as defined there (see the definition `Prop320Condition`).
--
--   This is the explicit characterization referred to in Theorem 1.1.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: "where C ∈ (3.146, 3.147) satisfies C − ln C = 2" → hypotheses C ∈ (3.146, 3.147) and C − log C = 2; reason: exactly one such C exists; same instances
--   - encoding: "A*_LB (A*_LA) … R*_LB (R*_LA) is the revenue of Bob when best-responding to it" → an optimal equalizer As with its parameter R (IsOptimalLargeBobEq / IsOptimalLargeAliceEq); reason: by Lemmas 3.13 and 3.18 Bob's best-response revenue against A^{LB}_R, A^{LA}_R is R; same instances
--   - reading: "A is a posted price of a − b" → A is essentially equivalent to a mechanism realizing FP(a − b); reason: uniqueness is up to essential equivalence (footnote 3, p.3; Definition 2.1)
--   - encoding: "its allocation rule is monotone" → monotonicity of z⁺_A on [0, ∞); reason: the condition is stated through z⁺_A, whose values the other clauses constrain; same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Proposition 3.20 and Definition 3.19, p.30 (PDF 33)

import Mathlib
import Definitions.Def_CompetingSellers_optA
import Definitions.Def_CompetingSellers_Prop320Condition

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Proposition 3.20 (characterization of Alice's optimal mechanisms).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Proposition 3.20, p.30 (PDF 33): "Consider an instance of the duopoly game in the main
model with fixed buyer values `a, b > 0` and let `∆ = |a − b|`. A mechanism `A` is optimal for
Alice if and only if the following condition holds, depending on the relation between `a` and
`b`: 1. When `0 < a < b`, … 2. When `b ≤ a < C · b`, where `C ∈ (3.146, 3.147)` satisfies
`C − ln C = 2`, … 3. When `C · b ≤ a`, `A` is a posted price of `a − b`." (the full condition is
`Prop320Condition`).

**Formalization Note.** `C` is any number in `(3.146, 3.147)` with `C − ln C = 2` (there is
exactly one). Item 3 is up to essential equivalence (footnote 3). -/
theorem proposition_3_20 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (C : ℝ) (hC : C ∈ Set.Ioo (3.146 : ℝ) 3.147)
    (hCl : C - Real.log C = 2) :
    ∀ A : Mech S null, IsAliceOptimal a b A ↔ Prop320Condition a b C A := by sorry

end CompetingSellers
