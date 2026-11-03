-- Prove2me | Theorems.Thm_EnvelopeMSLP_envelope_lp_ae
-- name    : EnvelopeMSLP.envelope_lp_ae
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:39.256418+00:00
-- url     : https://prove2.me/theorems/a5c2fb5d-dc6f-4b80-94f7-cde483ff3bf9
-- title:
--   §2, p.11 (corrected: tame data) — the envelope theorem applies almost everywhere, for all optimal pairs of one LP
-- statement:
--   For all $m,n$ there is a finite family $\mathfrak P$ of polynomials in the entries of $(A,b,c)$, chosen before $\Theta$ and the data, with the following property. Let $\Theta\subseteq\mathbb R$ be open and $A,b,c$ differentiable on $\Theta$, and let $Y$ be the exceptional set of $\mathfrak P$. If (6) is solvable at $\theta\in\Theta\setminus Y$, then a dual optimum exists at $\theta$, the value $V$ has a derivative at $\theta$, and
--   $$V'(\theta)=\langle\nabla c(\theta),x\rangle+\Big\langle y,\nabla b(\theta)-\tfrac{d}{d\theta}A(\theta)\,x\Big\rangle$$
--   for every primal optimum $x$ and every dual optimum $y$ at $\theta$. If the data are tame on $\Theta$, then $Y$ is Lebesgue null.
--
--   This removes the smooth-selection hypothesis of Theorem 1 at almost every $\theta$, and it is the one-LP statement that the multi-stage theorem reduces to.
--
--   Differences from the source:
--   - correction: Theorem 2 implies that V fails to be differentiable with probability zero → the conclusions hold off Y, and Y is null for tame data; reason: counterexample (p.7 example (3) with θ replaced by a C∞ map): Θ = (0,1), K ⊂ Θ a fat Cantor set, h C∞ with h⁻¹(0) = K, p = 1 − h, V(θ) = max ½p(θ)x + y s.t. x + y ≤ 1, −x − p(θ)y ≤ −1, −x ≤ 0, −y ≤ 0, 0 ≤ 2 + θ; the data are C∞, injective and bi-continuous, the problem is solvable at every θ, and V = 1 on K while V = p/2 < ½ off K, so V is discontinuous on a set of positive measure
--   - reading: the envelope theorem can be applied almost everywhere → at each solvable θ off Y: a dual optimum exists, V′ exists, and the formula holds for every optimal pair; reason: this is the precise content of applying Theorem 1 without its selection hypothesis
--   - reading: the set Y, defined in the proof of Theorem 2 → the exceptional set of a family with its own existential; reason: Y of the proof is a set of basis changes; the family depends only on (m, n), and the union of two families serves both statements
--   - encoding: A : Θ → R^{m×n}, b : Θ → R^m, c : Θ → R^n → A, b, c defined on all of ℝ, hypotheses on Θ; reason: every hypothesis and conclusion looks only at θ in the open set Θ or near such θ, so values off Θ are never used
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), §2, p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_FreeSolvable
import Definitions.Def_EnvelopeMSLP_FreeDualOptimal
import Definitions.Def_EnvelopeMSLP_freeValue
import Definitions.Def_EnvelopeMSLP_lpCurve
import Definitions.Def_EnvelopeMSLP_IsTameData
import Definitions.Def_EnvelopeMSLP_exceptionalSet
import Definitions.Def_EnvelopeMSLP_matDeriv
open Matrix

namespace EnvelopeMSLP

/-- **The envelope theorem applies almost everywhere, for one LP.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.11: "the envelope theorem can
be applied almost everywhere and the set `Y`, defined in the proof of Theorem 2, can be ignored". For all
`m`, `n` there is a finite polynomial family `𝔓`, fixed before `Θ` and the data, such that for every open `Θ`
and data differentiable on `Θ`, with `Y` the exceptional set: at each `θ ∈ Θ ∖ Y` where (6) is solvable, a
dual optimum exists, `V` has a derivative `V′`, and
`V′ = ⟨c′(θ), x⟩ + ⟨y, b′(θ) − A′(θ) x⟩` for **every** primal optimum `x` and **every** dual optimum `y`
at `θ`. If the data are tame, `Y` is null.

**Formalization Note.** The family carries its own `∃`: a solver can take the union with the family of
`theorem_2`, since enlarging `𝔓` only enlarges `Y`, and the proof needs nothing else about it. -/
theorem envelope_lp_ae (m n : ℕ) :
    ∃ 𝔓 : Finset (MvPolynomial (LPIndex m n) ℝ),
      ∀ (Θ : Set ℝ) (A : ℝ → Matrix (Fin m) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (c : ℝ → Fin n → ℝ),
        IsOpen Θ → (∀ k, DifferentiableOn ℝ (fun θ => lpCurve A b c θ k) Θ) →
        (∀ θ ∈ Θ \ exceptionalSet 𝔓 Θ (lpCurve A b c), FreeSolvable (A θ) (b θ) (c θ) →
          (∃ y, FreeDualOptimal (A θ) (b θ) (c θ) y) ∧
          ∃ V', HasDerivAt (fun θ' => (freeValue (A θ') (b θ') (c θ')).toReal) V' θ ∧
            ∀ x y, FreeOptimal (A θ) (b θ) (c θ) x → FreeDualOptimal (A θ) (b θ) (c θ) y →
              V' = deriv c θ ⬝ᵥ x + y ⬝ᵥ (deriv b θ - matDeriv A θ *ᵥ x)) ∧
        (IsTameData Θ (lpCurve A b c) →
          MeasureTheory.volume (exceptionalSet 𝔓 Θ (lpCurve A b c)) = 0) := by sorry

end EnvelopeMSLP
