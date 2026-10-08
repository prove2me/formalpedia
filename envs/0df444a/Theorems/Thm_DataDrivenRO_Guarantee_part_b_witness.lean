-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_part_b_witness
-- name    : DataDrivenRO.Guarantee.part_b_witness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:42:24.980953+00:00
-- url     : https://prove2.me/theorems/f465d7ae-3e6f-44b9-992f-b3f1802f13b7
-- title:
--   EC.1.1, proof of Theorem 1(b), p. ec1 — f(u,x) = vᵀu − x, x* = δ*(v|𝒰) is robust feasible but ℙ(f(ũ,x*) > 0) > ε
-- statement:
--   Let $0<\epsilon<1$, let $\mathbb P$ be a probability measure on $\mathbb R^d$, and let $\mathcal U\subseteq\mathbb R^d$ be nonempty. Suppose $\mathbf v\in\mathbb R^d$ is such that $\{\mathbf v^T\mathbf u:\mathbf u\in\mathcal U\}$ is bounded above (so $\delta^*(\mathbf v\mid\mathcal U)$ is finite) and $t>0$ satisfy
--   $$\delta^*(\mathbf v\mid\mathcal U)\le\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)-t .$$
--   Define $f(\mathbf u,x)=\mathbf v^T\mathbf u-x$ for $x\in\mathbb R$, and put $x^*=\delta^*(\mathbf v\mid\mathcal U)$. Then
--
--   1. $x^*$ is robust feasible: $f(\mathbf u,x^*)\le 0$ for all $\mathbf u\in\mathcal U$;
--   2. $\mathbb P\big(f(\tilde{\mathbf u},x^*)>0\big)=\mathbb P\big(\tilde{\mathbf u}^T\mathbf v>\delta^*(\mathbf v\mid\mathcal U)\big)>\epsilon$.
--
--   This is the counterexample of the proof of Theorem 1(b): a bi-affine constraint that is robustly satisfied on $\mathcal U$ but violated with probability more than $\epsilon$.
--
--   **Formalization Note** The scalar decision variable is `Fin 1 → ℝ` and $x$ is its single coordinate. Nonemptiness of $\mathcal U$ and boundedness above of $\{\mathbf v^T\mathbf u:\mathbf u\in\mathcal U\}$ are stated so that $\delta^*(\mathbf v\mid\mathcal U)$ is a real number (the published support function is a real supremum, $0$ on empty or unbounded-above images); the paper's hypothesis $\delta^*(\mathbf v\mid\mathcal U)\le\mathrm{VaR}-t$ already makes it finite, and the proof uses $x^*=\delta^*(\mathbf v\mid\mathcal U)$ as a real number. The page writes $\delta(\mathbf v\mid\mathcal U)$ for $\delta^*(\mathbf v\mid\mathcal U)$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.1, proof of Theorem 1(b), second paragraph, p. ec1

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- EC.1.1, proof of Theorem 1(b), p. ec1: if `U` is nonempty, `{vᵀu : u ∈ U}` is bounded above
(so `δ*(v|U)` is finite) and `δ*(v|U) ≤ VaR^ℙ_ε(v) − t` for some `t > 0`, then for `f(u, x) = vᵀu − x` (with `x ∈ ℝ¹`) the
point `x* = δ*(v|U)` is robust feasible, but `ℙ(f(ũ, x*) > 0) > ε`. -/
theorem part_b_witness {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Set (Fin d → ℝ)) (hne : U.Nonempty)
    (v : Fin d → ℝ) (hbdd : BddAbove ((fun u => u ⬝ᵥ v) '' U)) (t : ℝ) (ht : 0 < t)
    (hgap : RobustMDP.Shared.supportFunction U v ≤ VaR P ε v - t)
    (f : (Fin d → ℝ) → (Fin 1 → ℝ) → ℝ) (hfdef : ∀ u x, f u x = u ⬝ᵥ v - x 0)
    (xstar : Fin 1 → ℝ) (hxstar : xstar = fun _ => RobustMDP.Shared.supportFunction U v) :
    (∀ u ∈ U, f u xstar ≤ 0) ∧ ENNReal.ofReal ε < P {u | 0 < f u xstar} := by sorry

end DataDrivenRO.Guarantee
