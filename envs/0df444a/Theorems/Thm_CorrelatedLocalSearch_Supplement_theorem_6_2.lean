-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_6_2
-- name    : CorrelatedLocalSearch.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:10:04.317302+00:00
-- url     : https://prove2.me/theorems/38ccc7c9-8e4e-4f4d-a224-22ca01220f97
-- title:
--   Theorem 6.2 — synthesis of robust selection and restarts
-- statement:
--   Let $V$ be the unique optimizer of LP (15). The tie-breaking LP (33) selects a deterministic stationary action $\mu$ attaining, for every initial state and $D\ge1$, the exact minimax nontermination probability $\min\{1,DV(x)\}$ over all history-dependent selectors. A controlled same-tape restart policy from $x_0$ terminates robustly exactly when $V(x_0)<1$; the synthesized rule restarts on $S=\{V=1\}$ and has a uniform geometric tail. At $V(x_0)=1$, every policy is defeated. For rational powered coefficients, $V,\mu,S$ and explicit tail constants are computable in polynomial time.
--
--   Differences from the source:
--   - encoding: the two LPs and their tie-breaking construction → feasibility and optimizer predicates with the binding action equations stated explicitly; reason: spells out (15) and (33)
--   - encoding: polynomial time in the explicit state-action description → one Turing-machine procedure over canonical finite rational transition-table encodings, with exact LP, selector, restart-set and contraction-potential certificates; reason: formalizes the paper's uniform bit-complexity claim
--   - encoding: nontermination and restart-tail probabilities → `ENNReal`; reason: exact nonnegative encoding
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 6.2, p.16 (PDF p.18), App. D.2 pp.34–36 (PDF pp.36–38)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_RestartSynthesis

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 6.2, p.16 (PDF p.18), including
the tie-breaking LP (33), exact stationary minimax selection, the restart equivalence and geometric
tail, the impossibility clause, and exact polynomial-time synthesis for rational powered rows. -/
theorem theorem_6_2 {A X : Type*} [Fintype A] [Fintype X] [MeasurableSpace A]
    [MeasurableSingletonClass A] (hA : 2 ≤ Fintype.card A)
    (pi : A -> Real) (hpi : ∀ a, 0 < pi a) (hpisum : (∑ a, pi a) = 1)
    (s : Real) (hs0 : 0 < s) (hs1 : s ≤ 1) (M : FiniteProcess A X)
    (V : X -> Real) (hV : IsFirstLPOptimizer M pi s V) :
    ∃ psi : X -> Real, IsSecondLPOptimizer M pi s V psi ∧
      ∃ mu : X -> Nat,
        (∀ y, mu y ∈ M.actions y ∧ (V y < 1 -> IsTightAction M pi s V y (mu y)) ∧
          (V y < 1 -> psi y = 1 + ∑ z, if V z < 1
            then poweredTransition M pi s y (mu y) z * psi z else 0)) ∧
        (∀ x D, 1 ≤ D ->
          worstProbability pi s D
              (processNonterminationEvent M (fun _ y => mu y) x) =
            (⨅ sel : {sel : ProcessSelector A X // IsValidProcessSelector M sel},
              worstProbability pi s D (processNonterminationEvent M sel.1 x)) ∧
          worstProbability pi s D
              (processNonterminationEvent M (fun _ y => mu y) x) =
            min 1 (ENNReal.ofReal (D * V x))) ∧
        (∀ x0,
          ((∃ rho : ControlledRestartPolicy M x0,
              ∀ nu : Measure (Nat -> A), nu ∈ SourceClass pi s 1 ->
                nu {omega | controlledRestartTau rho omega = ⊤} = 0) ↔ V x0 < 1) ∧
          (V x0 < 1 -> ∃ rho : ControlledRestartPolicy M x0,
            UsesStationaryResetRule rho mu {y | V y = 1} ∧
            ∃ K gamma : Real, 0 ≤ K ∧ 0 < gamma ∧ gamma < 1 ∧
              ∀ D : Real, 1 ≤ D -> ∀ nu : Measure (Nat -> A), nu ∈ SourceClass pi s D ->
                ∀ t : Nat, nu {omega | (t : ℕ∞) < controlledRestartTau rho omega} ≤
                  ENNReal.ofReal (D * K * gamma ^ t)) ∧
          (V x0 = 1 -> ∀ rho : ControlledRestartPolicy M x0,
            ∃ nu : Measure (Nat -> A), nu ∈ SourceClass pi s 1 ∧
              nu {omega | controlledRestartTau rho omega = ⊤} = 1)) ∧
        ((∀ y f z, f ∈ M.actions y -> ∃ q : Rat, poweredTransition M pi s y f z = (q : Real)) ->
          PolynomialTimeSynthesizable M pi s V mu {y | V y = 1}) := by sorry

end CorrelatedLocalSearch.Supplement
