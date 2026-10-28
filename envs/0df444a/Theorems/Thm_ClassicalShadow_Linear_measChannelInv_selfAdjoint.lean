-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_measChannelInv_selfAdjoint
-- name    : ClassicalShadow.Linear.measChannelInv_selfAdjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:42.813491+00:00
-- url     : https://prove2.me/theorems/97569f0c-5164-4f34-94d9-27d10f8dc2ce
-- title:
--   p. 12, proof of Lemma 1 — M⁻¹ is self-adjoint: tr(XM⁻¹(Y)) = tr(M⁻¹(X)Y)
-- statement:
--   Let $\mathcal U$ be a finite, tomographically complete measurement primitive on $n$ qubits, with measurement channel $\mathcal M$ and inverse $\mathcal M^{-1}$. Then $\mathcal M^{-1}$ is self-adjoint with respect to the trace pairing: for all $2^n\times 2^n$ complex matrices $X, Y$,
--   $$\operatorname{tr}\big(X\,\mathcal M^{-1}(Y)\big) = \operatorname{tr}\big(\mathcal M^{-1}(X)\,Y\big).$$
--
--   This identity moves $\mathcal M^{-1}$ from the shadow onto the observable, turning $\operatorname{tr}(O_0\hat\rho)$ into the diagonal entry $\langle \hat b|U\mathcal M^{-1}(O_0)U^\dagger|\hat b\rangle$ in the proof of Lemma 1.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 12, proof of Lemma 1, before (S9)

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem measChannelInv_selfAdjoint {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hE : TomographicallyComplete E) (X Y : Op n) :
    (X * measChannelInv E Y).trace = (measChannelInv E X * Y).trace := by sorry
end ClassicalShadow.Linear
