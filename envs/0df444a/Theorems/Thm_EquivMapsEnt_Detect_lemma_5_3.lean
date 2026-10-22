-- Prove2me | Theorems.Thm_EquivMapsEnt_Detect_lemma_5_3
-- name    : EquivMapsEnt.Detect.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:31.866904+00:00
-- url     : https://prove2.me/theorems/6b8eda00-3529-4252-8a42-6125e993936f
-- title:
--   Lemma 5.3: the lift is unitarily equivariant and preserves t-positivity
-- statement:
--   Let $\phi:M_n(\mathbb C)\to M_N(\mathbb C)$ be complex linear and let $\mu$ be a finite left invariant Borel measure on $U_n$. On $H=L^2(U_n,\mathbb C^N;\mu)$, write $V(W)\psi(U)=\psi(W^{-1}U)$ and let $F_X$ be the form of the fibrewise lift $\Phi(X)\psi(U)=\phi(U^*XU)\psi(U)$. Each $V(W)$ is a surjective linear isometry, the actions obey $V(W_1W_2)=V(W_1)V(W_2)$, and
--
--   $$F_{WXW^*}(V(W)\psi,V(W)\chi)=F_X(\psi,\chi).$$
--
--   If $\phi$ is $t$-positive, then the block quadratic form of $\Phi$ on $\mathbb C^t\otimes H$ is nonnegative for every positive semidefinite input. This is the infinite dimensional equivariant detector used before finite dimensional compression.
--
--   **Formalization Note** The form is used in place of a bundled bounded operator. Finite measure and square integrability make its integrand integrable; the statement concerns all $L^2$ vectors, including their almost everywhere equivalence classes.
-- source:
--   Bardet, Collins & Sapra, Characterization of equivariant maps and application to entanglement detection, arXiv:1811.08193v3, p. 13, Lemma 5.3 (proof p. 14)

import Definitions.Def_EquivMapsEnt_Detect_Lift

namespace EquivMapsEnt.Detect

open MeasureTheory
open scoped Matrix ComplexOrder

/-- Lemma 5.3: covariance of the fibrewise lift, and preservation of t-positivity. -/
theorem lemma_5_3 {n N : ℕ}
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ))
    [μ.IsMulLeftInvariant] [IsFiniteMeasure μ] (t : ℕ) :
    (∀ W : Matrix.unitaryGroup (Fin n) ℂ,
      Function.Surjective (regRep (N := N) μ W)) ∧
    (∀ (W₁ W₂ : Matrix.unitaryGroup (Fin n) ℂ) (ψ : LiftSpace n N μ),
      regRep (N := N) μ (W₁ * W₂) ψ =
        regRep (N := N) μ W₁ (regRep (N := N) μ W₂ ψ)) ∧
    (∀ (W : Matrix.unitaryGroup (Fin n) ℂ)
      (X : Matrix (Fin n) (Fin n) ℂ) (ψ χ : LiftSpace n N μ),
      liftForm φ μ ((W : Matrix (Fin n) (Fin n) ℂ) * X * star (W : Matrix (Fin n) (Fin n) ℂ))
        (regRep μ W ψ) (regRep μ W χ) = liftForm φ μ X ψ χ) ∧
    (IsTPositive t φ → IsTPositiveLift t φ μ) := by sorry

end EquivMapsEnt.Detect
