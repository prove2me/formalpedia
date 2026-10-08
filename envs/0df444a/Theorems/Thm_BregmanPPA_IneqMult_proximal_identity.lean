-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_proximal_identity
-- name    : BregmanPPA.IneqMult.proximal_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:37.196497+00:00
-- url     : https://prove2.me/theorems/fa43d7f2-c370-47d1-b3ab-10f9353a02ac
-- title:
--   Theorem 7 proof — multiplier recursion is a Bregman proximal step
-- statement:
--   Under the standing conditions for problem (10), the Bregman function and the positive step sizes, every sequence satisfying recursion (11) is a Bregman proximal-point run for the subdifferential of the negative dual functional:
--
--   $$c_k^{-1}(\nabla h(p^k)-\nabla h(p^{k+1}))\in\partial(-d)(p^{k+1})\qquad(k\ge0).$$
--
--   This identifies the operator to which Theorem 1 applies.
--
--   **Formalization Note** The multiplier sequence is explicitly kept inside $S$. The dual functional is extended-real valued; the run's monotone conjugate uses real values justified by Lemma 3.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 217, proof of Theorem 7, final displayed equivalence, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Run

open Filter Topology

namespace BregmanPPA.IneqMult

/-- The last displayed equivalence in the proof of Theorem 7, p. 217: (11) is a
Bregman proximal point run for the subdifferential of the negative dual functional. -/
theorem proximal_identity {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m)
    (hP : IsConvexProgram C f g)
    (hd : ∃ q : E m, dualFn C f g q ≠ ⊥)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S)
    (hc : ∀ k, 0 < c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p) :
    BregmanPPA.Convergence.IsBregmanPPARun S h (BregmanPPA.Convergence.subdiffOp (fun q => -(dualFn C f g q))) c p := by sorry

end BregmanPPA.IneqMult
