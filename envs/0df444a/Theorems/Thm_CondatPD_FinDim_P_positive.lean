-- Prove2me | Theorems.Thm_CondatPD_FinDim_P_positive
-- name    : CondatPD.FinDim.P_positive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:40:12.557173+00:00
-- url     : https://prove2.me/theorems/e0eb8c36-3e93-4693-a635-f37bc87616e5
-- title:
--   §4, proof of Theorem 3.3, p. 12 — under στ‖L‖² ≤ 1 the operators P and P′ are positive
-- statement:
--   Let $\mathcal X,\mathcal Y$ be real Hilbert spaces, $L:\mathcal X\to\mathcal Y$ bounded linear, and $\tau>0$, $\sigma>0$ with
--   $$\sigma\tau\|L\|^2\le1 .$$
--   Then for every $x\in\mathcal X$, $y\in\mathcal Y$,
--   $$\Big\langle x,\tfrac1\tau x-L^*y\Big\rangle+\Big\langle y,-Lx+\tfrac1\sigma y\Big\rangle\ge0\quad\text{and}\quad\Big\langle x,\tfrac1\tau x+L^*y\Big\rangle+\Big\langle y,Lx+\tfrac1\sigma y\Big\rangle\ge0,$$
--   that is, $\langle z,Pz\rangle_I\ge0$ and $\langle z,P'z\rangle_I\ge0$ for every $z=(x,y)$, where $P$ is the operator (20) and $P'$ the operator of (44).
--
--   With equality $\sigma\tau\|L\|^2=1$ allowed, $P$ is only positive, not strictly positive, so it does not define an inner product; this is the situation the proof of Theorem 3.3 has to handle.
--
--   **Formalization Note** The claim for $P'$ is the one the proof for Algorithm 3.2 uses ("replacing $P$ by $P'$", p. 13). Finite dimension is not assumed.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 12, §4, proof of Theorem 3.3 for Algorithm 3.1, before (32); p. 13, (44)

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open InnerProductSpace

namespace CondatPD.FinDim

/-- Proof of Theorem 3.3 (p. 12): under (i) `στ‖L‖² ≤ 1`, the operators `P` of (20) and `P′`
of (44) are positive, `⟨z, P z⟩_I ≥ 0` and `⟨z, P′ z⟩_I ≥ 0` for every `z = (x, y)`. -/
theorem P_positive {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hi : σ * τ * ‖L‖ ^ 2 ≤ 1) :
    ∀ (x : X) (y : Y), 0 ≤ qP τ σ L x y ∧ 0 ≤ qP' τ σ L x y := by sorry

end CondatPD.FinDim
