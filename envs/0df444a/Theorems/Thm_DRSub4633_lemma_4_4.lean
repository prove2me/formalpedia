-- Prove2me | Theorems.Thm_DRSub4633_lemma_4_4
-- name    : DRSub4633.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:57:48.089788+00:00
-- url     : https://prove2.me/theorems/bf1a2a99-17e5-4df0-b92a-4d46072a07aa
-- title:
--   Lemma 4.4 — signed endpoint inequality
-- statement:
--   Let $J$ be continuously differentiable and DR-submodular on $[0,1]^m$ and let $p\in(0,1)^m$. For $0\le i\le m$ let $P_i^-$ and $P_i^+$ agree with $p$ in the first $i$ coordinates and equal $0$, respectively $1$, in the others, and set
--   $$A_i(J)=\frac{J(P_i^-)-J(P_{i-1}^-)}{p_i},\qquad B_i(J)=\frac{J(P_{i-1}^+)-J(P_i^+)}{1-p_i}.$$
--   Then every $o\in[0,1]^m$ satisfies
--   $$J(o)\le J(p)-\sum_{i=1}^m p_iB_i(J)+\sum_{i=1}^m\big[(1-p_i)A_i(J)+p_iB_i(J)\big]o_i. \tag{30}$$
--
--   This is the large-coordinate comparison: one affine function of $o$, built from secants along two chains, dominates $J$.
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: coordinates 1, …, m → Fin m, 0-based; P^±_k agrees with p on coordinates of index < k; reason: Lean convention; same instances
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.4, pp.15–16

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular

namespace DRSub4633

/-- **Lemma 4.4 (Signed endpoint inequality).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.4, pp.15–16: "Let `J` be `C¹`
and DR-submodular on `[0, 1]^m`, and let `p ∈ (0, 1)^m`. For `0 ≤ i ≤ m`, let `P⁻ᵢ` and `P⁺ᵢ` agree
with `p` in the first `i` coordinates and equal `0` and `1`, respectively, in the others. With
`Aᵢ(J) = [J(P⁻ᵢ) − J(P⁻ᵢ₋₁)]/pᵢ`, `Bᵢ(J) = [J(P⁺ᵢ₋₁) − J(P⁺ᵢ)]/(1 − pᵢ)`, every `o ∈ [0, 1]^m`
satisfies `J(o) ≤ J(p) − ∑ᵢ pᵢBᵢ(J) + ∑ᵢ [(1 − pᵢ)Aᵢ(J) + pᵢBᵢ(J)]oᵢ`. (30)"

**Formalization Note.** Coordinates are `Fin m`, in their order; coordinate `i` (0-based) is the
`(i+1)`-st, so `P^±_k` agrees with `p` on the coordinates of index `< k`. -/
theorem lemma_4_4 {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (hJ : GeomDRSub.IsDRSubmodular J)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (o : EuclideanSpace ℝ (Fin m)) (ho : o ∈ GeomDRSub.cube m) :
    let Pm : ℕ → EuclideanSpace ℝ (Fin m) := fun k => WithLp.toLp 2 (fun j => if j.val < k then p j else 0)
    let Pp : ℕ → EuclideanSpace ℝ (Fin m) := fun k => WithLp.toLp 2 (fun j => if j.val < k then p j else 1)
    let A : Fin m → ℝ := fun i => (J (Pm (i.val + 1)) - J (Pm i.val)) / p i
    let B : Fin m → ℝ := fun i => (J (Pp i.val) - J (Pp (i.val + 1))) / (1 - p i)
    J o ≤ J (WithLp.toLp 2 p) - ∑ i, p i * B i + ∑ i, ((1 - p i) * A i + p i * B i) * o i := by sorry

end DRSub4633
