-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_lemma3
-- name    : BregmanPPA.IneqMult.lemma3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:56.096979+00:00
-- url     : https://prove2.me/theorems/8e07804a-d8dd-420b-ab15-b4f58989e51c
-- title:
--   Lemma 3 — the Bregman monotone conjugate is finite and differentiable
-- statement:
--   If $h$ is a Bregman function whose zone and gradient image each contain the strictly positive orthant, then its monotone conjugate is closed, proper, convex, everywhere finite, and differentiable:
--
--   $$h^{*+}:\mathbb R^m\to\mathbb R,\qquad h^{*+}\text{ is convex and differentiable everywhere}.$$
--
--   This is the well-posedness result for the objective and gradient appearing in the multiplier recursion.
--
--   **Formalization Note** The conjugate itself is extended-real valued, with explicit exclusion of both infinite values; differentiability is then stated for its real-valued version.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 216, Lemma 3, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology InertialFB.IFB

namespace BregmanPPA.IneqMult

/-- Lemma 3, p. 216: the monotone conjugate is closed, proper, convex, finite, and smooth. -/
theorem lemma3 {m : ℕ} (S : Set (E m)) (h : E m → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) :
    LowerSemicontinuous (monoConj h) ∧
    IsProperFn (monoConj h) ∧
    IsConvexFn (monoConj h) ∧
    (∀ z : E m, monoConj h z ≠ ⊤ ∧ monoConj h z ≠ ⊥) ∧
    Differentiable ℝ (fun z : E m => (monoConj h z).toReal) := by sorry

end BregmanPPA.IneqMult
