-- Prove2me | Theorems.Thm_FiniteStateContract_Equivalence_theorem_3_6
-- name    : FiniteStateContract.Equivalence.theorem_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:15:52.797676+00:00
-- url     : https://prove2.me/theorems/06c531c2-c6bd-4270-868d-e0ec8f580ac2
-- title:
--   Theorem 3.6 — Two-way Nash equilibrium and McKean–Vlasov BSDE correspondence
-- statement:
--   Under the §2 setting and Assumptions 2.1 and 3.1, let $(r,\xi)$ be any contract. Every solution $(Y,Z,\alpha,p,Q)$ of (22)–(25), in the class of Definition 3.5, induces a Nash equilibrium $(\alpha,p)$ for that contract.
--
--   Conversely, every Nash equilibrium $(\hat\alpha,\hat p)$ is represented by a solution $(Y,Z,\alpha,p,Q)$ satisfying
--   $$\alpha=\hat\alpha\quad dP\otimes dt\text{-almost everywhere},\qquad p(t)=\hat p(t)\quad dt\text{-almost everywhere}.$$
--   The flow in a solution is pointwise consistent with its law, whereas the converse promises only the stated almost-everywhere agreement with the given equilibrium. Both directions are included in one item.
--
--   Differences from the source:
--   - encoding: basis-vector states and paths on [0,T] → Fin m labels and nonnegative real time, with canonical paths frozen after T; reason: the published path space is in bijection with the source space; the initial simplex vector excludes m=0 and retains m=1
--   - reading: the right side of (15) is written with a hat → evaluate the unminimized Hamiltonian H at its unique minimizer; reason: the printed argument count and preceding sentence uniquely identify H; recorded in insight I4
--   - encoding: expectations and optimization costs are written as numerical quantities → graphs of signed extended integrals with measurable integrands and no infinity-minus-infinity value; reason: undefined quantities are not assigned a default zero; asserted identities include definedness
--   - encoding: the controlled density solves the Doléans exponential equation → the exact exponential compensator times the product of rates over jumps; reason: this is the closed form of the same density on finite-state càdlàg paths; it is not normalized
--   - reading: Definition 3.5 omits dt after the time-integral integrands → ordinary Lebesgue time integration of Y squared and the squared state seminorm of Z; reason: the integral signs and limits specify time integration, as confirmed in the proof on p. 8
--   - encoding: feedback controls are defined only on [0,T] → the feedback agrees on [0,T] and is zero after T; reason: predictability is expressed on nonnegative time; a fixed extension prevents unconstrained data beyond T from changing admissibility
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), Theorem 3.6, PDF p. 7 = printed p. 7; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Definitions.Def_FiniteStateContract_Equivalence_BSDE

open MeasureTheory
open scoped NNReal

namespace FiniteStateContract.Equivalence

theorem theorem_3_6 {m l : ℕ} {T : ℝ≥0} (D : Data m l T) (a : Feedback m l)
    (hS : Setting D) (h21 : Assumption21 D) (h31 : Assumption31 D a)
    (K : Contract m T) (hK : IsContract D K) :
    (∀ Y Z α p Q, MeanFieldBackward D a K Y Z α p Q → Nash D K α p) ∧
    (∀ α₀ p₀, Nash D K α₀ p₀ →
      ∃ Y Z α p Q, MeanFieldBackward D a K Y Z α p Q ∧
        (∀ᵐ x ∂(D.P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          α x.2.toNNReal x.1 = α₀ x.2.toNNReal x.1) ∧
        (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), p t.toNNReal = p₀ t.toNNReal)) := by sorry

end FiniteStateContract.Equivalence
