-- Prove2me | Theorems.Thm_EnvelopeMSLP_theorem_2
-- name    : EnvelopeMSLP.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:12.685504+00:00
-- url     : https://prove2.me/theorems/ba4d2911-2664-4686-b5eb-913d2ef48b32
-- title:
--   Theorem 2 (corrected: tame data, Y in a finite union of boundaries) — the LP value is smooth off a small set
-- statement:
--   For all $m,n$ there is a finite family $\mathfrak P$ of polynomials in the entries of $(A,b,c)$, chosen before $\Theta$ and the data, with the following property. Let $\Theta\subseteq\mathbb R$ be open, let $A,b,c$ be continuous on $\Theta$, let
--   $$V(\theta)=\max_x\ \langle c(\theta),x\rangle\quad\text{s.t. }A(\theta)x\le b(\theta),$$
--   and let $Y=\Theta\cap\bigcup_{p\in\mathfrak P}\partial\{\theta\in\Theta:p(A(\theta),b(\theta),c(\theta))=0\}$.
--
--   1. Every $\theta\in\Theta\setminus Y$ has a neighbourhood on which (6) is infeasible throughout, or unbounded throughout, or solvable throughout.
--   2. If (6) is solvable at $\theta\in\Theta\setminus Y$, then $V$ is differentiable at $\theta$ when the data are differentiable on $\Theta$, and $C^r$ at $\theta$ when the data are $C^r$ on $\Theta$, for every $r$.
--   3. If the data are tame on $\Theta$, then $Y$ is Lebesgue null.
--   4. If each boundary in the family is finite within $\Theta$, then $Y$ is finite.
--
--   The value of a linear program is therefore smooth away from a set controlled by finitely many polynomials in the data.
--
--   Differences from the source:
--   - correction: invertible bi-continuous data, non-differentiability points finite → differentiability only off Y, with Y null for tame data; continuous data for clause 1; reason: counterexample (p.7 example (3) with θ replaced by a C∞ map): Θ = (0,1), K ⊂ Θ a fat Cantor set, h C∞ with h⁻¹(0) = K, p = 1 − h, V(θ) = max ½p(θ)x + y s.t. x + y ≤ 1, −x − p(θ)y ≤ −1, −x ≤ 0, −y ≤ 0, 0 ≤ 2 + θ; the data are C∞, injective and bi-continuous, the problem is solvable at every θ, and V = 1 on K while V = p/2 < ½ off K, so V is discontinuous on a set of positive measure
--   - correction: the exceptional set is finite → Y is finite when the boundaries of the family are; reason: V(θ) = max{x : x ≤ sin θ, x ≤ 0, 0·x ≤ 2 + eᶿ} = min(sin θ, 0) on Θ = ℝ has infinitely many kinks, with analytic injective data
--   - correction: V smooth for invertible bi-continuous data → differentiable or Cʳ only when the data are; reason: with W continuous and nowhere differentiable, V(θ) = max{x : x ≤ W(θ), 0·x ≤ 2 + θ} = W(θ) is nowhere differentiable
--   - generalization: Θ connected; A, b, c invertible and bi-continuous → Θ open; no invertibility; reason: the proof does not use them, and tame data with these properties are covered
--   - reading: the set of θ where V is not differentiable → differentiability is claimed at solvable θ, and clause 1 classifies the rest; reason: V is ±∞ near an infeasible or unbounded θ, so differentiability has no meaning there
--   - encoding: V(θ) smooth at θ → the EReal value read through toReal, ContDiffAt r for every r : WithTop ℕ∞; reason: near a solvable θ ∉ Y the value is finite by clause 1
--   - encoding: A : Θ → R^{m×n}, b : Θ → R^m, c : Θ → R^n → A, b, c defined on all of ℝ, hypotheses on Θ; reason: every hypothesis and conclusion looks only at θ in the open set Θ or near such θ, so values off Θ are never used
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 2, display (6), p.10

import Mathlib
import Definitions.Def_EnvelopeMSLP_FreeFeasible
import Definitions.Def_EnvelopeMSLP_FreeSolvable
import Definitions.Def_EnvelopeMSLP_freeValue
import Definitions.Def_EnvelopeMSLP_lpCurve
import Definitions.Def_EnvelopeMSLP_IsTameData
import Definitions.Def_EnvelopeMSLP_exceptionalSet
open Topology Filter

namespace EnvelopeMSLP

/-- **Theorem 2 (corrected): the value of an LP off the exceptional set.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Theorem 2, p.10, which is
false as printed. For all `m`, `n` there is a finite family `𝔓` of polynomials in the entries of `(A, b, c)`,
fixed before `Θ` and the data, such that for every open `Θ` and all `A, b, c` continuous on `Θ`, with
`Y = Θ ∩ ⋃_{p ∈ 𝔓} ∂{θ ∈ Θ : p(A(θ), b(θ), c(θ)) = 0}`:
1. near each `θ ∈ Θ ∖ Y`, form (6) is infeasible throughout, or unbounded throughout, or solvable
   throughout;
2. if (6) is solvable at `θ ∈ Θ ∖ Y`, then `V` is differentiable at `θ` when the data are differentiable on
   `Θ`, and `C^r` at `θ` when the data are `C^r` on `Θ`, for every `r`;
3. `Y` is null if the data are tame;
4. `Y` is finite if each boundary in the family is finite within `Θ`.

**Formalization Note.** `V` is `freeValue` read in `ℝ`, the true value near a solvable `θ` by clause 1. -/
theorem theorem_2 (m n : ℕ) :
    ∃ 𝔓 : Finset (MvPolynomial (LPIndex m n) ℝ),
      ∀ (Θ : Set ℝ) (A : ℝ → Matrix (Fin m) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (c : ℝ → Fin n → ℝ),
        IsOpen Θ → (∀ k, ContinuousOn (fun θ => lpCurve A b c θ k) Θ) →
        (∀ θ ∈ Θ \ exceptionalSet 𝔓 Θ (lpCurve A b c),
          ((∀ᶠ θ' in 𝓝 θ, ∀ x, ¬ FreeFeasible (A θ') (b θ') x) ∨
            (∀ᶠ θ' in 𝓝 θ, freeValue (A θ') (b θ') (c θ') = ⊤) ∨
            (∀ᶠ θ' in 𝓝 θ, FreeSolvable (A θ') (b θ') (c θ'))) ∧
          (FreeSolvable (A θ) (b θ) (c θ) →
            ((∀ k, DifferentiableOn ℝ (fun θ' => lpCurve A b c θ' k) Θ) →
              DifferentiableAt ℝ (fun θ' => (freeValue (A θ') (b θ') (c θ')).toReal) θ) ∧
            ∀ r : WithTop ℕ∞, (∀ k, ContDiffOn ℝ r (fun θ' => lpCurve A b c θ' k) Θ) →
              ContDiffAt ℝ r (fun θ' => (freeValue (A θ') (b θ') (c θ')).toReal) θ)) ∧
        (IsTameData Θ (lpCurve A b c) →
          MeasureTheory.volume (exceptionalSet 𝔓 Θ (lpCurve A b c)) = 0) ∧
        ((∀ p ∈ 𝔓, (Θ ∩ frontier {θ | θ ∈ Θ ∧ MvPolynomial.eval (lpCurve A b c θ) p = 0}).Finite) →
          (exceptionalSet 𝔓 Θ (lpCurve A b c)).Finite) := by sorry

end EnvelopeMSLP
