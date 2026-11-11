-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_4_5
-- name    : AcceptSubcube.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:09.435194+00:00
-- url     : https://prove2.me/theorems/305c55d9-0e19-42b8-9d7a-1950de265cf6
-- title:
--   Lemma 4.5 — bias preservation at constant cost: $F_0+V\'\le16V$
-- statement:
--   Let $\Phi$ be a weighted unary/binary CNF on $q$ variables with nonnegative rational weights, and let rational singleton and pair laws be given that are consistent (a moment vector whose local laws on at most two variables are nonnegative), with fractional cost $V$. A deterministic polynomial-time procedure outputs pins (each variable pinned at most once, only variables $<q$) such that:
--
--   1. every literal $u$ with $\mathbb P[u=1]<1/4$ is pinned false;
--   2. after simplifying (delete clauses with a literal pinned true, remove literals pinned false), with $F_0$ the weight of clauses made permanently false and $V'$ the fractional cost of the residual formula under the same, unconditioned laws,
--   $$F_0+V'\le16V .$$
--
--   No conditioning is performed and the laws of unpinned variables are unchanged. The lemma enforces the bias condition of Lemma 4.4 at a constant-factor cost.
--
--   Differences from the source:
--   - reading: pins some variables and simplifies the formula → output = a list of pins; simplification = the rule of the proof (delete clauses with a literal pinned true, remove literals pinned false); reason: the lemma does not spell out "simplifies"; the proof fixes it
--   - encoding: consistent rational singleton and pair laws → a rational moment list with nonnegative local laws on at most two of the variables; reason: moments parametrize exactly the normalized consistent laws
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.5, p.19 (simplification rule: proof, p.19)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_RelaxFeasible
import Definitions.Def_AcceptSubcube_WCNF
import Definitions.Def_AcceptSubcube_encInst

namespace AcceptSubcube

/-- **Lemma 4.5 (Bias preservation at constant cost).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.5, p.19: "Let Φ be a weighted
unary/binary CNF on q variables with nonnegative rational weights and consistent rational singleton
and pair laws, of fractional cost V. A deterministic polynomial-time procedure pins some variables
and simplifies the formula so that, with F₀ the weight of clauses made permanently false and V′ the
fractional cost of the residual formula under the unconditioned restrictions of the input laws,
F₀ + V′ ≤ 16V. (13) Every literal u with P[u = 1] < 1/4 is pinned false, and the laws of unpinned
variables are unchanged; no conditioning is performed."

A deterministic polynomial-time map from `(q, Φ, laws)` to a list of pins such that: every variable
is pinned at most once and only variables `< q` are pinned; every literal of marginal `< 1/4` is
pinned false; and, simplifying as in the proof (delete clauses with a literal pinned true, remove
literals pinned false), `F₀ + V′ ≤ 16V`.

**Formalization Note.** The laws are a rational moment list whose local laws on at most two of the
variables `0, …, q−1` are nonnegative (`LocalNonneg 2 q`); the moment parametrization makes the
singleton and pair laws normalized and consistent. `V′` is the fractional cost of the residual
formula under the same laws (unconditioned; the laws of unpinned variables are unchanged by
construction). -/
theorem lemma_4_5 :
    ∃ pin : ℕ × List (ℚ × List (ℕ × Bool)) × List (List ℕ × ℚ) → List (ℕ × Bool),
      Nonempty (Turing.TM2ComputableInPolyTime encPinIn encPins pin) ∧
      ∀ (q : ℕ) (Φ : WCNF) (L : List (List ℕ × ℚ)),
        IsUnaryBinary Φ → NonnegWeights Φ → OnVars Φ (Finset.range q) → LocalNonneg 2 q L →
          ((pin (q, Φ, L)).map Prod.fst).Nodup ∧
          (∀ p ∈ pin (q, Φ, L), p.1 < q) ∧
          (∀ i < q, ∀ b : Bool, lit1 L i b < 1 / 4 → pinVal (pin (q, Φ, L)) i = some (!b)) ∧
          pinF0 (pin (q, Φ, L)) Φ + fracCost L (pinResidual (pin (q, Φ, L)) Φ) ≤
            16 * fracCost L Φ := by sorry

end AcceptSubcube
