-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_5_3
-- name    : DeMorganApprox.Main.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:00.782695+00:00
-- url     : https://prove2.me/theorems/95eb274b-6efd-456c-ba15-26430aaf50a1
-- title:
--   Lemma 5.3 — OR/AND gate composition with (A+1)B = (A₁+1)B₁ + (A₂+1)B₂
-- statement:
--   Let $P_1,P_2$ be vector-form span programs on orthogonal ambient spaces $H_1,H_2$ computing Boolean functions $f_1,f_2$, with unit targets $u_1,u_2$, all listed vectors unit, and witness parameters $(A_1,B_1)$, $(A_2,B_2)$ (so $A_i,B_i\ge1$). Let $P$ be the OR composition (resp. AND composition) of Lemma 5.3, with angle $\theta$ and parameters $(A,B)$:
--
--   * OR: $\cos^2\theta=\frac{A_1+1}{A_1+A_2+2}$, $A=A_1+A_2+1$, $B=\cos^2\theta B_1+\sin^2\theta B_2$;
--   * AND: $\cos^2\theta=\frac{B_1}{B_1+B_2}$, $A=\cos^2\theta A_1+\sin^2\theta A_2$, $B=B_1+B_2$.
--
--   Then, in each case,
--
--   1. $P$ computes $f_1\vee f_2$ (resp. $f_1\wedge f_2$);
--   2. $P$ is vector-form: the target and all listed vectors are unit;
--   3. the target is $u=c\,u_1+s\,u_2\in H_1\oplus^\perp H_2$ with $c,s\ge0$;
--   4. $P$ lists every vector of $P_1$ and of $P_2$ with its label; the OR program adds exactly one always-available vector, the AND program none;
--   5. $(A,B)$ are witness parameters of $P$, and
--   $$(A+1)B=(A_1+1)B_1+(A_2+1)B_2 .$$
--
--   The identity in 5 is the additive invariant that the heavy-chain construction accumulates along a chain.
--
--   Differences from the source:
--   - encoding: two programs whose ambient spaces are orthogonal, and the direct sum of the child ambient spaces → programs on coordinate types ι₁ and ι₂ and the parent on ι₁ ⊕ ι₂, child vectors extended by zero; reason: an orthogonal direct sum of coordinate spaces is the coordinate space of the disjoint union
--   - encoding: a real Euclidean space H with unit vectors and the entrywise absolute value abs(V) → the coordinate space ι → ℝ for a finite type ι with its standard basis; squared norms are sums of squares; reason: abs(V) is only defined relative to a fixed orthonormal basis, which the construction provides (leaf and helper coordinates); finitely many listed vectors span a finite-dimensional subspace
--   - reading: If (A, B) are the witness parameters of the parent target, then (A+1)B = (A₁+1)B₁ + (A₂+1)B₂ → the explicit (A, B) of the proof (orParams, andParams) are witness parameters of the parent and satisfy the identity; reason: Definition 3.2 makes parameters upper bounds, so the literal reading is false: for two leaf programs under OR the construction gives (3, 1) and 4·1 = 2 + 2, but (4, 1) are also witness parameters and 5·1 ≠ 4; the proof (PDF pp. 18–20) defines A and B explicitly, and that is what Lemma 5.5 uses
--   - generalization: there is a vector-form span program computing f₁ ∨ f₂ (resp. f₁ ∧ f₂) → the explicit compositions orCompose and andCompose of the proof have all the stated properties; reason: the defined program is a witness of the source's existential, so the Lean statement implies it
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.3, PDF p. 17 (printed p. 15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; statement continues on PDF p. 18; proof PDF pp. 18–20 (printed pp. 16–18)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_GateComposition

namespace DeMorganApprox.Main

open SpanProgram

/-- Lemma 5.3, PDF pp. 17–18 (printed pp. 15–16); proof PDF pp. 18–20. Orthogonal ambient
spaces are encoded as the coordinate type `ι₁ ⊕ ι₂`; `(A, B)` are the parameters the
construction produces (`orParams`, `andParams`). -/
theorem lemma_5_3 {m : ℕ} {ι₁ ι₂ J₁ J₂ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype J₁]
    [Fintype J₂] (P₁ : SpanProgram m ι₁ J₁) (P₂ : SpanProgram m ι₂ J₂)
    (f₁ f₂ : (Fin m → Bool) → Bool) (A₁ B₁ A₂ B₂ : ℝ)
    (hv₁ : P₁.IsVectorForm) (hv₂ : P₂.IsVectorForm)
    (hc₁ : P₁.Computes f₁) (hc₂ : P₂.Computes f₂)
    (hw₁ : P₁.HasWitnessParams A₁ B₁) (hw₂ : P₂.HasWitnessParams A₂ B₂) :
    -- OR gate
    ((P₁.orCompose P₂ A₁ A₂).Computes (fun x => f₁ x || f₂ x) ∧
      (P₁.orCompose P₂ A₁ A₂).IsVectorForm ∧
      (∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧
        (P₁.orCompose P₂ A₁ A₂).target = Sum.elim (c • P₁.target) (s • P₂.target)) ∧
      (∀ j, (P₁.orCompose P₂ A₁ A₂).vec (.inl (.inl j)) = Sum.elim (P₁.vec j) (0 : ι₂ → ℝ) ∧
        (P₁.orCompose P₂ A₁ A₂).label (.inl (.inl j)) = P₁.label j) ∧
      (∀ j, (P₁.orCompose P₂ A₁ A₂).vec (.inl (.inr j)) = Sum.elim (0 : ι₁ → ℝ) (P₂.vec j) ∧
        (P₁.orCompose P₂ A₁ A₂).label (.inl (.inr j)) = P₂.label j) ∧
      (P₁.orCompose P₂ A₁ A₂).label (.inr ()) = Label.always ∧
      (P₁.orCompose P₂ A₁ A₂).HasWitnessParams
        (orParams A₁ B₁ A₂ B₂).1 (orParams A₁ B₁ A₂ B₂).2 ∧
      ((orParams A₁ B₁ A₂ B₂).1 + 1) * (orParams A₁ B₁ A₂ B₂).2 =
        (A₁ + 1) * B₁ + (A₂ + 1) * B₂) ∧
    -- AND gate
    ((P₁.andCompose P₂ B₁ B₂).Computes (fun x => f₁ x && f₂ x) ∧
      (P₁.andCompose P₂ B₁ B₂).IsVectorForm ∧
      (∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧
        (P₁.andCompose P₂ B₁ B₂).target = Sum.elim (c • P₁.target) (s • P₂.target)) ∧
      (∀ j, (P₁.andCompose P₂ B₁ B₂).vec (.inl j) = Sum.elim (P₁.vec j) (0 : ι₂ → ℝ) ∧
        (P₁.andCompose P₂ B₁ B₂).label (.inl j) = P₁.label j) ∧
      (∀ j, (P₁.andCompose P₂ B₁ B₂).vec (.inr j) = Sum.elim (0 : ι₁ → ℝ) (P₂.vec j) ∧
        (P₁.andCompose P₂ B₁ B₂).label (.inr j) = P₂.label j) ∧
      (P₁.andCompose P₂ B₁ B₂).HasWitnessParams
        (andParams A₁ B₁ A₂ B₂).1 (andParams A₁ B₁ A₂ B₂).2 ∧
      ((andParams A₁ B₁ A₂ B₂).1 + 1) * (andParams A₁ B₁ A₂ B₂).2 =
        (A₁ + 1) * B₁ + (A₂ + 1) * B₂) := by sorry

end DeMorganApprox.Main
