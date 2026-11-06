-- Prove2me | Theorems.Thm_BlockBochner_lemma_9
-- name    : BlockBochner.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:11.151324+00:00
-- url     : https://prove2.me/theorems/a06ba526-fb48-420d-bb5c-6f96177aba5c
-- title:
--   Lemma 9 — compression and Schur complements
-- statement:
--   Let $H=U\oplus V$ be an orthogonal decomposition of a real Hilbert space into closed subspaces, and let $A$ be bounded and self-adjoint with $0<aI\preceq A\preceq bI$. Write $A=\begin{pmatrix}A_{UU}&A_{UV}\\A_{VU}&A_{VV}\end{pmatrix}$. Then:
--   1. $A_{UU}$ and $(A^{-1})_{UU}$ are boundedly invertible, with $aI_U\preceq A_{UU}\preceq bI_U$ and $b^{-1}I_U\preceq(A^{-1})_{UU}\preceq a^{-1}I_U$.
--   2. $K_U=((A^{-1})_{UU})^{-1}$ satisfies $K_U=A_{UU}-A_{UV}A_{VV}^{-1}A_{VU}$ and $aI_U\preceq K_U\preceq A_{UU}\preceq bI_U$ (the subtracted term is omitted when $V=\{0\}$).
--   3. For every $x\in U$,
--   $$\min_{z\in H,\ P_Uz=x}\langle z,A^{-1}z\rangle=\langle x,A_{UU}^{-1}x\rangle;$$
--   in particular $\langle z,A^{-1}z\rangle\ge\langle P_Uz,A_{UU}^{-1}P_Uz\rangle$ for every $z\in H$.
--
--   Moreover, compression preserves operator order, while inversion reverses operator order for bounded, uniformly positive self-adjoint operators.
--
--   **Formalization Note** $V=U^\perp$; inverses are `Ring.inverse` and "boundedly invertible" is being a unit in the algebra of bounded operators on $U$; $\preceq$ is the order of quadratic forms; the minimum is attained.
--
--   Differences from the source:
--   - reading: A⁻¹_UU in part 3 → (A_UU)⁻¹; reason: the other reading (A⁻¹)_UU makes part 3 false whenever A_UV ≠ 0, and the proof of Theorem 21 applies part 3 as (B̃_TaTa)⁻¹ in (12), p.25
--   - encoding: "minimum" over z with P_U z = x → IsLeast of the set of values; reason: attainment is part of "min"
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Lemma 9, pp.13–14

import Mathlib
import Definitions.Def_BlockBochner_blk

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Lemma 9 (compression and Schur complements).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Lemma 9, pp.13–14. Let `H = U ⊕ V` be an
orthogonal decomposition into closed subspaces and `A` bounded self-adjoint with `0 < aI ⪯ A ⪯ bI`.
1. `A_{UU}` and `(A⁻¹)_{UU}` are boundedly invertible, `aI_U ⪯ A_{UU} ⪯ bI_U`,
   `b⁻¹I_U ⪯ (A⁻¹)_{UU} ⪯ a⁻¹I_U`.
2. `K_U = ((A⁻¹)_{UU})⁻¹ = A_{UU} − A_{UV} A_{VV}⁻¹ A_{VU}` and `aI_U ⪯ K_U ⪯ A_{UU} ⪯ bI_U`
   (the subtracted term is omitted when `V = {0}`).
3. For every `x ∈ U`, `min_{z : P_U z = x} ⟨z, A⁻¹z⟩ = ⟨x, A_{UU}⁻¹ x⟩`; in particular
   `⟨z, A⁻¹z⟩ ≥ ⟨P_U z, A_{UU}⁻¹ P_U z⟩` for every `z ∈ H`.
Moreover, compression preserves operator order, and inversion reverses operator order for bounded,
uniformly positive self-adjoint operators.

**Formalization Note** `V = U^⊥`; `A_{UV} = blk A U V`; inverses are `Ring.inverse`, and
"boundedly invertible" is `IsUnit` in the algebra of bounded operators on `U`. `A⁻¹_{UU}` in part 3
is read as `(A_{UU})⁻¹` (the other reading `(A⁻¹)_{UU}` makes part 3 false whenever `A_{UV} ≠ 0`;
the proof of Theorem 21, (12) on p.25, uses `(B̃_{T_aT_a})⁻¹`). "min" is attained (`IsLeast`).
`⪯` is the order of quadratic forms. -/
theorem lemma_9 (U : ClosedSubmodule ℝ H) (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) {a b : ℝ}
    (ha : 0 < a) (hlo : ∀ x, a * ‖x‖ ^ 2 ≤ inner ℝ x (A x))
    (hhi : ∀ x, inner ℝ x (A x) ≤ b * ‖x‖ ^ 2) :
    let U' : Submodule ℝ H := U
    let V' : Submodule ℝ H := U'ᗮ
    (IsUnit (blk A U' U') ∧ IsUnit (blk (Ring.inverse A) U' U') ∧
      ∀ x : U', a * ‖x‖ ^ 2 ≤ inner ℝ x (blk A U' U' x) ∧ inner ℝ x (blk A U' U' x) ≤ b * ‖x‖ ^ 2 ∧
        b⁻¹ * ‖x‖ ^ 2 ≤ inner ℝ x (blk (Ring.inverse A) U' U' x) ∧
        inner ℝ x (blk (Ring.inverse A) U' U' x) ≤ a⁻¹ * ‖x‖ ^ 2) ∧
    (Ring.inverse (blk (Ring.inverse A) U' U') =
        blk A U' U' - blk A U' V' ∘L Ring.inverse (blk A V' V') ∘L blk A V' U' ∧
      ∀ x : U', a * ‖x‖ ^ 2 ≤ inner ℝ x (Ring.inverse (blk (Ring.inverse A) U' U') x) ∧
        inner ℝ x (Ring.inverse (blk (Ring.inverse A) U' U') x) ≤ inner ℝ x (blk A U' U' x) ∧
        inner ℝ x (blk A U' U' x) ≤ b * ‖x‖ ^ 2) ∧
    (∀ x : U', IsLeast
        {r | ∃ z : H, U'.orthogonalProjectionOnto z = x ∧ r = inner ℝ z (Ring.inverse A z)}
        (inner ℝ x (Ring.inverse (blk A U' U') x))) ∧
    (∀ z : H, inner ℝ (U'.orthogonalProjectionOnto z)
        (Ring.inverse (blk A U' U') (U'.orthogonalProjectionOnto z)) ≤ inner ℝ z (Ring.inverse A z)) ∧
    (∀ A₁ A₂ : H →L[ℝ] H, IsSelfAdjoint A₁ → IsSelfAdjoint A₂ →
        (∀ x, inner ℝ x (A₁ x) ≤ inner ℝ x (A₂ x)) →
        ∀ x : U', inner ℝ x (blk A₁ U' U' x) ≤ inner ℝ x (blk A₂ U' U' x)) ∧
    (∀ A₁ A₂ : H →L[ℝ] H, IsSelfAdjoint A₁ → IsSelfAdjoint A₂ →
        (∃ c > 0, ∀ x, c * ‖x‖ ^ 2 ≤ inner ℝ x (A₁ x)) →
        (∀ x, inner ℝ x (A₁ x) ≤ inner ℝ x (A₂ x)) →
        ∀ x, inner ℝ x (Ring.inverse A₂ x) ≤ inner ℝ x (Ring.inverse A₁ x)) := by sorry

end BlockBochner
