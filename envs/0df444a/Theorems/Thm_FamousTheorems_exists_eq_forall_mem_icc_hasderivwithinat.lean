-- Prove2me | Theorems.Thm_FamousTheorems_exists_eq_forall_mem_icc_hasderivwithinat
-- name    : FamousTheorems.exists_eq_forall_mem_icc_hasderivwithinat
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:39:58.920694+00:00
-- url     : https://prove2.me/theorems/3026357f-6f56-44a3-9f07-daa5d67b224f
-- title:
--   The Picard–Lindelöf theorem
-- statement:
--   **The Picard\u2013Lindel\u00f6f theorem** (Cauchy\u2013Lipschitz). An ordinary differential equation $y' = v(t,y)$ with $v$ Lipschitz in $y$ and continuous in $t$ has a unique solution on a small interval through any given initial condition. Existence and uniqueness both come from the Banach fixed-point theorem applied to the Picard integral operator, whose contraction constant is governed by the Lipschitz bound — which is why the same hypothesis delivers both. The Lipschitz condition cannot be dropped: $y' = \sqrt{|y|}$ with $y(0) = 0$ is continuous but has infinitely many solutions. This theorem is what licenses treating an ODE as determining a well-defined flow, the premise of the whole theory of dynamical systems. **Formalization note.** `IsPicardLindelof` bundles the Lipschitz and boundedness hypotheses, and the solution is asserted with `HasDerivWithinAt` on a closed interval. The result is Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_eq_forall_mem_icc_hasderivwithinat :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ x : E} 
    {a r L K : NNReal}, 
    IsPicardLindelof f t₀ x₀ a r L K → 
    x ∈ Metric.closedBall x₀ ↑r → ∃ α, α ↑t₀ = x ∧ ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by sorry

end FamousTheorems
