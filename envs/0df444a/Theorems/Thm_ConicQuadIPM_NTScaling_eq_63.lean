-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_eq_63
-- name    : ConicQuadIPM.NTScaling.eq_63
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:26.710292+00:00
-- url     : https://prove2.me/theorems/b3495276-e3fa-49fc-b050-218ff4a8aca5
-- title:
--   (63), Appendix p. 39 — for the rotated cone, Ŵ = TWT satisfies ŴQ̂Ŵ = Q̂ and ŝ = θ²Ŵ²x̂
-- statement:
--   Let $d\ge2$, let $T$, $Q$ be the matrices (18), (19) of the rotated quadratic cone, and put $\hat Q := TQT$, $\hat W := TWT$, $\hat x := Tx$, $\hat s := Ts$ for a matrix $W$ and vectors $x,s\in\mathbb R^d$. Then for every $\theta\in\mathbb R$:
--   1. if $WQW = Q$ then $\hat W\hat Q\hat W = \hat Q$;
--   2. if $s = \theta^2W^2x$ then
--   $$\hat s = \theta^2\,\hat W^2\,\hat x.\qquad(63)$$
--
--   These identities transport the NT condition for the rotated cone to the quadratic cone, where (31) applies.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The page writes $\hat\theta^2$ in the last two members of (63) and then shows $\hat\theta = \theta$ (formalized in `rot_hat_quantities`); here (63) is stated with $\theta$. The page's $\bar W^i\hat Q^i\hat W^i$ is a printed slip for $\hat W^i\hat Q^i\hat W^i$. The facts $TT = I$, $T^T = T$ the page uses are consequences of (18), not hypotheses.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 39, Appendix, proof of Lemma 4.2, (63)

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- (63), Appendix, proof of Lemma 4.2, p. 39 (rotated quadratic cone): with `Q̂ = TQT` and
`Ŵ = TWT`, `WQW = Q` gives `ŴQ̂Ŵ = Q̂`, and `s = θ²W²x` gives `ŝ = θ²Ŵ²x̂` for `x̂ = Tx`,
`ŝ = Ts`. -/
theorem eq_63 (d : ℕ) (hd : 2 ≤ d) (W : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ)
    (x s : Fin d → ℝ) :
    (W * Qmat .rot d * W = Qmat .rot d →
      (Tmat .rot d * W * Tmat .rot d) * (Tmat .rot d * Qmat .rot d * Tmat .rot d) *
          (Tmat .rot d * W * Tmat .rot d) =
        Tmat .rot d * Qmat .rot d * Tmat .rot d) ∧
    (s = θ ^ 2 • ((W * W) *ᵥ x) →
      Tmat .rot d *ᵥ s =
        θ ^ 2 • (((Tmat .rot d * W * Tmat .rot d) * (Tmat .rot d * W * Tmat .rot d)) *ᵥ
          (Tmat .rot d *ᵥ x))) := by sorry
end ConicQuadIPM.NTScaling
