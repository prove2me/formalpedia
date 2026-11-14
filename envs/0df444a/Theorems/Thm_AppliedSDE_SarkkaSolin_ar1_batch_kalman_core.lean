-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_kalman_core
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_kalman_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T21:16:19.158204+00:00
-- url     : https://prove2.me/theorems/1b230031-7f34-4971-8d05-2f91cf171bd9
-- title:
--   AR(1) Gaussian-process batch posterior equals recursive scalar Kalman estimate
-- statement:
--   Let 0<a<1, V>0, and r>0. On time indices 0,...,n define the stationary AR(1) covariance K_ij = V*a^|i-j|. Start the scalar Kalman filter at covariance P0=Vr/(V+r) and mean m0=V/(V+r)*y0. At each subsequent observation use AR(1) predicted variance a²P+V(1−a²), posterior variance predicted*r/(predicted+r), and innovation gain predicted/(predicted+r). Then the final recursive Kalman posterior mean equals the last component of the batch GP regression vector K(K+rI)⁻¹ y. This nontrivial matrix/Schur-complement identity is the core of the published Applied SDE OU/GP/Kalman capstone b005e2e3-7db8-49d7-975f-8d9aaaedb8b2, after applying the already Proved OU covariance grid–AR(1) power lemma b9c2bf08-5edb-4a03-93af-04d8e8892d44. The conclusion is not among the hypotheses.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10.6 and 12.4 (scalar Kalman recursions and exact OU/GP regression equivalence), pp. 216–218 and 265–266. https://doi.org/10.1017/9781108186735

import Mathlib
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.ar1_batch_kalman_core
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y m P : Fin (n + 1) → ℝ) :
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ k : Fin n,
      let predicted : ℝ := a ^ 2 * P k.castSucc + V * (1 - a ^ 2)
      P k.succ = predicted * r / (predicted + r) ∧
      m k.succ = a * m k.castSucc +
        predicted / (predicted + r) *
          (y k.succ - a * m k.castSucc)) →
    m (Fin.last n) =
      K.mulVec (((K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹).mulVec y)
        (Fin.last n) := by
  sorry
