-- Prove2me | Theorems.Thm_FiniteStateContract_Equivalence_lemma_3_4
-- name    : FiniteStateContract.Equivalence.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:15:50.784165+00:00
-- url     : https://prove2.me/theorems/066316a1-4e09-4663-b560-773706a10752
-- title:
--   Lemma 3.4 — Both BSDE representations and feedback optimality
-- statement:
--   Under the §2 setting and Assumptions 2.1 and 3.1, fix any contract $(r,\xi)$, any predictable admissible control $\alpha$, and any measurable simplex-valued flow $p$.
--
--   1. Equation (20), with the running-payment index read as $s$, admits a unique solution $(Y,Z)$ in the backward solution class. For every such solution,
--   $$J_{r,\xi}(\alpha,p)=E^P[Y_0].$$
--   2. Equation (21), with the same reading, admits a unique solution. For every such solution,
--   $$\inf_{\beta\in\mathbb A}J_{r,\xi}(\beta,p)=E^P[Y_0],$$
--   and $\hat\alpha_t=\hat a(t,X_{t-},Z_t,p(t))$ is an admissible optimal control attaining this value.
--
--   Both existence clauses, both uniqueness clauses, both value identities, and feedback attainment are asserted. No boundedness of payments, integrability of $U(\xi)$, or additional regularity of running costs is assumed.
--
--   Differences from the source:
--   - encoding: basis-vector states and paths on [0,T] → Fin m labels and nonnegative real time, with canonical paths frozen after T; reason: the published path space is in bijection with the source space; the initial simplex vector excludes m=0 and retains m=1
--   - reading: the right side of (15) is written with a hat → evaluate the unminimized Hamiltonian H at its unique minimizer; reason: the printed argument count and preceding sentence uniquely identify H; recorded in insight I4
--   - encoding: expectations and optimization costs are written as numerical quantities → graphs of signed extended integrals with measurable integrands and no infinity-minus-infinity value; reason: undefined quantities are not assigned a default zero; asserted identities include definedness
--   - encoding: the controlled density solves the Doléans exponential equation → the exact exponential compensator times the product of rates over jumps; reason: this is the closed form of the same density on finite-state càdlàg paths; it is not normalized
--   - reading: Definition 3.5 omits dt after the time-integral integrands → ordinary Lebesgue time integration of Y squared and the squared state seminorm of Z; reason: the integral signs and limits specify time integration, as confirmed in the proof on p. 8
--   - encoding: a unique BSDE solution → Y indistinguishability and equality of Z in the integrated squared-seminorm quotient; reason: the martingale integral does not identify constant-vector components of Z; the proof on p. 8 uses this quotient
--   - reading: equations (20) and (21) use u(r_t) inside an integral in s → the driver uses u(r_s); reason: the surrounding equations specify the running index; the printed index fails the value identity in insight I2
--   - encoding: infima with empty-set value +infinity and potentially unbounded costs → EReal infima, with +infinity for empty families and -infinity for unbounded-below families; reason: real infima would return inappropriate default values
--   - encoding: feedback controls are defined only on [0,T] → the feedback agrees on [0,T] and is zero after T; reason: predictability is expressed on nonnegative time; a fixed extension prevents unconstrained data beyond T from changing admissibility
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), Lemma 3.4, PDF p. 6 = printed p. 6; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Definitions.Def_FiniteStateContract_Equivalence_BSDE

open MeasureTheory
open scoped NNReal

namespace FiniteStateContract.Equivalence

theorem lemma_3_4 {m l : ℕ} {T : ℝ≥0} (D : Data m l T) (a : Feedback m l)
    (hS : Setting D) (h21 : Assumption21 D) (h31 : Assumption31 D a)
    (K : Contract m T) (hK : IsContract D K) (α : Proc m T (Action l))
    (hα : IsControl D α) (p : Flow m) (hp : IsFlow (T := T) p) :
    ((∃ Y Z, Backward D K (frozenDriver D K α p) Y Z) ∧
      UniqueBackward D K (frozenDriver D K α p) ∧
      ∀ Y Z, Backward D K (frozenDriver D K α p) Y Z →
        ∃ v, IntegralValue D.P (fun ω => (Y 0 ω : EReal)) v ∧ AgentCost D K α p v) ∧
    ((∃ Y Z, Backward D K (optimizedDriver D a K.r p) Y Z) ∧
      UniqueBackward D K (optimizedDriver D a K.r p) ∧
      ∀ Y Z, Backward D K (optimizedDriver D a K.r p) Y Z →
        ∃ v, IntegralValue D.P (fun ω => (Y 0 ω : EReal)) v ∧
          InfimumValue (IsControl D) (fun β c => AgentCost D K β p c) v ∧
          Optimal D K (feedbackControl a Z p) p ∧
          AgentCost D K (feedbackControl a Z p) p v) := by sorry

end FiniteStateContract.Equivalence
