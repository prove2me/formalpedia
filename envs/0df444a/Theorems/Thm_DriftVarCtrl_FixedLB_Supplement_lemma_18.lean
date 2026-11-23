-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_lemma_18
-- name    : DriftVarCtrl.FixedLB.Supplement.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:47:03.657337+00:00
-- url     : https://prove2.me/theorems/beba8625-28d5-4a49-a01e-6b331c27fe80
-- title:
--   Lemma 18, p. EC-31 — verification lemma of the free lower boundary case (analytic form)
-- statement:
--   Let $V:\mathbb R\to\mathbb R$ be $C^1$ on $(-\infty,U)$ and continuous on $(-\infty,U]$, and $C^2$ at every $x<U$ outside a finite set $E$, with $V$, $V'$, $V''$ bounded there, $V(U)=M$, and for every $x<U$ outside $E$
--   $$\min\Bigl\{h_1+\mu_1V'(x)+\frac{\sigma_1^2}{2}V''(x),\;h_2+\mu_2V'(x)+\frac{\sigma_2^2}{2}V''(x),\;R(x)-V(x)\Bigr\}\ge0, \tag{193}$$
--   where $R(x)=0$ for $x<U$.
--
--   1. (194) For every stopping interval policy and every value $W$ of it, $V(x)\le W(x)$ for all $x\le U$.
--   2. (195) If a stopping interval policy $\pi^*$ attains the minimum outside $E$, that is $V(x)=0$ for $x<z_0^*$ and $h_{i_j}+\mu_{i_j}V'(x)+\frac{\sigma_{i_j}^2}{2}V''(x)=0$ on each piece $(S_{j-1},S_j)$ of $\pi^*$, then $V$ is the value of $\pi^*$ and $\pi^*$ is optimal.
--
--   The lemma closes the proofs of Theorem 4 (a) and (c): a candidate value built from smooth pasting is checked against (193).
--
--   **Formalization Note** The expectations of (194)–(195) are replaced by the analytic value of a stopping interval policy (definition `FreeModel`); the stochastic statement needs Itô's formula, which Mathlib lacks. The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source:
--
--   - encoding: the value of a policy is the expected cost (112) of the controlled diffusion → the analytic value IsStopValue: zero at and below the stopping level z₀, C¹ on [z₀, U], equal to M at U, and on each open piece C² and solving hᵢ + μᵢW′ + σᵢ²/2·W″ = 0; reason: Mathlib has no stochastic integral; this is the boundary-value system (115), (143)–(144), (162)–(167) the paper itself writes for every policy, as in the base mission's IsValue
--   - generalization: V(0) = 0 in (192) → no condition at 0; reason: neither conclusion uses V(0) = 0 (V ≤ 0 below U and V(U) = M already bound V − W at both ends of [z₀, U]); every V of the page (continuous at U, see the reading below) satisfies the Lean hypotheses, and the primary-system policies of Theorem 4 with a stopping level below 0 have V(0) < 0
--   - reading: min{h(A*(x)) + μ(A*(x))V′(x) + σ(A*(x))²/2 V″(x), R(A*(x)) − V(A*(x))} = 0 for all but finitely many x → V = 0 below the stopping level of π*, and the ODE of the control of π* on each of its pieces, outside E; reason: the printed R(A*(x)) − V(A*(x)) applies R and V to a control; the condition is the stopping-region / continuation-region split of (148), (144), (158), (165), (167), which the proofs of Theorem 4 check
--   - encoding: μ : I → ∆, σ : I → Ψ, h : I → Λ bounded functions → the constants μᵢ, σᵢ, hᵢ of the model; reason: two controls with constant coefficients; boundedness holds trivially
--   - reading: V is C¹ and piecewise C² on (−∞, U) with V(U) = M (192) → V is C¹ on (−∞, U), continuous on (−∞, U] and C² off the finite set E; reason: V(U) = M is the boundary value (115) of the value function, which is continuous at U; a V with a jump at U (V = 0 below U, V(U) = M) satisfies the literal hypotheses but violates (194), since a policy stopping just below x near U has value close to M < 0
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-31, Lemma 18, (192)–(195)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 18, the verification lemma of the free lower boundary case, analytic form (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…),
p. EC-31, (192)–(195)). Let `V` be `C¹` on `(−∞, U)`, continuous on `(−∞, U]` and `C²` off a
finite set `E`, with
`V, V′, V″` bounded, `V(U) = M` and, off `E` on `(−∞, U)`,
`min{h₁ + μ₁V′ + σ₁²/2 V″, h₂ + μ₂V′ + σ₂²/2 V″, R − V} ≥ 0` (193), where `R = 0` below `U`.
Then (194) `V ≤ W` on `(−∞, U]` for the value `W` of every stopping interval policy. Moreover
(195), if a stopping interval policy `π*` attains the minimum off `E` (`V = R = 0` where it stops,
the ODE of its control where it continues), then `V` is the value of `π*` and `π*` is optimal.

Formalization Note: the expectations in (194)–(195) are replaced by the analytic value
`IsStopValue` of a stopping interval policy; the stochastic statement needs Itô's formula, which
Mathlib lacks. The printed hypothesis `V(0) = 0` (192) is dropped: the conclusions hold without it,
and the primary-system policies of Theorem 4 with a stopping level below `0` have `V(0) < 0`.
The printed `min{h(A*(x)) + …, R(A*(x)) − V(A*(x))} = 0` is read as: `V = 0` on the stopping
region of `π*` and the ODE of the control of `π*` on each of its pieces. The bounded `μ, σ, h` of
the page are constants here. The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem lemma_18 (p : Params) (hv : v p .one < v p .two) (V : ℝ → ℝ) (E : Finset ℝ)
    (hV1 : ContDiffOn ℝ 1 V (Set.Iio p.U)) (hVc : ContinuousOn V (Set.Iic p.U))
    (hV2 : ∀ x < p.U, x ∉ E → ContDiffAt ℝ 2 V x)
    (hbdd : ∃ B : ℝ, (∀ x < p.U, |V x| ≤ B ∧ |deriv V x| ≤ B) ∧
      ∀ x < p.U, x ∉ E → |deriv (deriv V) x| ≤ B)
    (hUM : V p.U = p.M)
    (hHJB : ∀ x < p.U, x ∉ E →
      (∀ c : Ctrl, 0 ≤ p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x) ∧
      V x ≤ 0) :
    (∀ (π : StopPolicy p) (W : ℝ → ℝ), IsStopValue p π W → ∀ x ≤ p.U, V x ≤ W x) ∧
    ∀ πs : StopPolicy p,
      (∀ x < πs.S 0, x ∉ E → V x = 0) →
      (∀ (j : Fin πs.k) (x : ℝ), x ∈ Set.Ioo (πs.S j.castSucc) (πs.S j.succ) → x ∉ E →
        p.cost (πs.ctrl j) + p.mu (πs.ctrl j) * deriv V x
          + p.sig (πs.ctrl j) ^ 2 / 2 * deriv (deriv V) x = 0) →
      IsStopValue p πs V ∧ IsStopOptimal p πs := by sorry

end DriftVarCtrl.FixedLB.Supplement
