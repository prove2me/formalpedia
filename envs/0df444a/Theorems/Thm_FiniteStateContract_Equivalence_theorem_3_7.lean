-- Prove2me | Theorems.Thm_FiniteStateContract_Equivalence_theorem_3_7
-- name    : FiniteStateContract.Equivalence.theorem_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:16:23.221584+00:00
-- url     : https://prove2.me/theorems/0830ed65-98a4-4071-bb5b-cfca876c14fc
-- title:
--   Theorem 3.7 — Optimal contracting equals McKean–Vlasov control
-- statement:
--   For every reservation threshold $\kappa\in\mathbb R$, under the §2 setting and Assumptions 2.1 and 3.1, the original contracting problem (11) and the forward McKean–Vlasov control problem (34) have a common defined extended-real value:
--   $$\widetilde V(\kappa)=V(\kappa).$$
--   The original value takes the infimum over all contracts admitting equilibria and then over equilibria meeting the weak expected-cost constraint. The forward value takes the infimum over random initial values with $E^P[Y_0]\le\kappa$, all predictable payment streams, and the entire first-moment $H_X^2$ class printed on p. 8. Each forward input must have a solution-derived, selection-independent cost; the inverse utility at $-Y_T$ must be defined almost surely. These are obligations of the assertion, not extra hypotheses.
--
--   Arbitrary compact subsets of $\mathbb R^l$, infinite population, continuous time, history-dependent contracts, boundary initial distributions, singleton state spaces, empty feasible sets, and both signs of infinite value are retained. The inverse-domain and moment-class findings I1 and I3 remain present in the printed target.
--
--   Differences from the source:
--   - encoding: basis-vector states and paths on [0,T] → Fin m labels and nonnegative real time, with canonical paths frozen after T; reason: the published path space is in bijection with the source space; the initial simplex vector excludes m=0 and retains m=1
--   - reading: the right side of (15) is written with a hat → evaluate the unminimized Hamiltonian H at its unique minimizer; reason: the printed argument count and preceding sentence uniquely identify H; recorded in insight I4
--   - encoding: expectations and optimization costs are written as numerical quantities → graphs of signed extended integrals with measurable integrands and no infinity-minus-infinity value; reason: undefined quantities are not assigned a default zero; asserted identities include definedness
--   - encoding: the controlled density solves the Doléans exponential equation → the exact exponential compensator times the product of rates over jumps; reason: this is the closed form of the same density on finite-state càdlàg paths; it is not normalized
--   - encoding: infima with empty-set value +infinity and potentially unbounded costs → EReal infima, with +infinity for empty families and -infinity for unbounded-below families; reason: real infima would return inappropriate default values
--   - reading: equation (34) denotes its solution and uses U inverse → each printed control has a solution and all its solutions yield one defined cost, with a unique inverse preimage almost surely; reason: no solution selection is specified; definedness and selection independence are asserted rather than assumed or enforced by deleting controls
--   - encoding: feedback controls are defined only on [0,T] → the feedback agrees on [0,T] and is zero after T; reason: predictability is expressed on nonnegative time; a fixed extension prevents unconstrained data beyond T from changing admissibility
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), Theorem 3.7, PDF p. 9 = printed p. 9; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Definitions.Def_FiniteStateContract_Equivalence_Values

open scoped NNReal

namespace FiniteStateContract.Equivalence

theorem theorem_3_7 {m l : ℕ} {T : ℝ≥0} (D : Data m l T) (a : Feedback m l)
    (hS : Setting D) (h21 : Assumption21 D) (h31 : Assumption31 D a) (κ : ℝ) :
    ∃ v : EReal, OriginalValue D κ v ∧ ForwardValue D a κ v := by sorry

end FiniteStateContract.Equivalence
