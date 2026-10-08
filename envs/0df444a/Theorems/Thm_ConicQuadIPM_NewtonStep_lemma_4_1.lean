-- Prove2me | Theorems.Thm_ConicQuadIPM_NewtonStep_lemma_4_1
-- name    : ConicQuadIPM.NewtonStep.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:52.314979+00:00
-- url     : https://prove2.me/theorems/6c2b91ab-b4d1-408d-8618-e0ad4ba3119c
-- title:
--   Lemma 4.1, p. 13 — a Newton step of length α scales the three residuals and the complementarity gap by 1 − α(1 − γ)
-- statement:
--   Let $K = K^1\times\cdots\times K^k$ be a product of cones, each the half-line $\mathbb R_+$, a quadratic cone or a rotated quadratic cone, with $n^i = 1$ for $\mathbb R_+$, $n^i\ge1$ for a quadratic cone and $n^i\ge2$ for a rotated one. Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, let $(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)})$ be any point and $\gamma\in[0,1]$, and let $(d_x,d_\tau,d_y,d_s,d_\kappa)$ solve the Newton system (22):
--   $$
--   \begin{aligned}
--   A d_x - b d_\tau &= (\gamma-1)(Ax^{(0)} - b\tau^{(0)}),\\
--   A^Td_y + d_s - c d_\tau &= (\gamma-1)(A^Ty^{(0)} + s^{(0)} - c\tau^{(0)}),\\
--   -c^Td_x + b^Td_y - d_\kappa &= (\gamma-1)(-c^Tx^{(0)} + b^Ty^{(0)} - \kappa^{(0)}),\\
--   X^{(0)}Td_s + S^{(0)}Td_x &= -X^{(0)}S^{(0)}e + \gamma\mu^{(0)}e,\\
--   \tau^{(0)}d_\kappa + \kappa^{(0)}d_\tau &= -\tau^{(0)}\kappa^{(0)} + \gamma\mu^{(0)},
--   \end{aligned}
--   $$
--   where $X^{(0)} = \operatorname{diag}(\operatorname{mat}(T^ix^{(0)i}))$, $S^{(0)} = \operatorname{diag}(\operatorname{mat}(T^is^{(0)i}))$, $T = \operatorname{diag}(T^i)$, $e$ stacks the first unit vectors and $\mu^{(0)} = ((x^{(0)})^Ts^{(0)} + \tau^{(0)}\kappa^{(0)})/(k+1)$. For a step size $\alpha\in[0,1]$ let $(x^{(1)},\tau^{(1)},y^{(1)},s^{(1)},\kappa^{(1)}) = (x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)}) + \alpha(d_x,d_\tau,d_y,d_s,d_\kappa)$ as in (23). Then
--   $$
--   \begin{aligned}
--   Ax^{(1)} - b\tau^{(1)} &= (1-\alpha(1-\gamma))(Ax^{(0)} - b\tau^{(0)}),\\
--   A^Ty^{(1)} + s^{(1)} - c\tau^{(1)} &= (1-\alpha(1-\gamma))(A^Ty^{(0)} + s^{(0)} - c\tau^{(0)}),\\
--   -c^Tx^{(1)} + b^Ty^{(1)} - \kappa^{(1)} &= (1-\alpha(1-\gamma))(-c^Tx^{(0)} + b^Ty^{(0)} - \kappa^{(0)}),\\
--   d_x^Td_s + d_\tau d_\kappa &= 0,\\
--   (x^{(1)})^Ts^{(1)} + \tau^{(1)}\kappa^{(1)} &= (1-\alpha(1-\gamma))\big((x^{(0)})^Ts^{(0)} + \tau^{(0)}\kappa^{(0)}\big).
--   \end{aligned}
--   $$
--
--   The lemma says that one Newton step moves the homogeneous model's infeasibility and its complementarity gap toward zero at exactly the same rate $1-\alpha(1-\gamma)$. This is the basis of the convergence analysis of the homogeneous algorithm and of its stopping criteria.
--
--   **Formalization Note** Indices are 0-based and vectors are stored block by block; $Ax = \sum_iA^ix^i$, $(A^Ty)^i = (A^i)^Ty$, $c^Tx = \sum_i(c^i)^Tx^i$, and the second identity of (22) and of the conclusion is stated block by block, as is the fourth line of (22). Three printed slips are corrected: the third line of (22) prints $\kappa$ for $\kappa^{(0)}$ (with a free $\kappa$ the third identity is false); the fourth identity of (24) prints $d_x^Td_s^T$ for $d_x^Td_s$; and the proof's constant $(\gamma-1)\mu^{(0)}k$ on p. 14 should be $(\gamma-1)\mu^{(0)}(k+1)$ (this affects only the proof). The dimension conventions are the paper's implicit ones and are needed: without them a block of dimension $0$ breaks $e^Te = k$. The hypotheses $\alpha\in[0,1]$ (from (23)) and $\gamma\in[0,1]$ (from (21)) are kept as on the page, although the identities hold for all real $\alpha$, $\gamma$. No interiority of the current point is assumed, as in the lemma.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 13, Lemma 4.1, (24); system (22) p. 12, step (23) p. 13; proof pp. 13–14

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

theorem lemma_4_1
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (x1 : (i : Fin k) → Fin (n i) → ℝ) (τ1 : ℝ) (y1 : Fin m → ℝ)
    (s1 : (i : Fin k) → Fin (n i) → ℝ) (κ1 : ℝ)
    (hx1 : ∀ i, x1 i = x0 i + α • dx i) (hτ1 : τ1 = τ0 + α * dτ)
    (hy1 : y1 = y0 + α • dy) (hs1 : ∀ i, s1 i = s0 i + α • ds i)
    (hκ1 : κ1 = κ0 + α * dκ) :
    (∑ i, A i *ᵥ x1 i) - τ1 • b = (1 - α * (1 - γ)) • ((∑ i, A i *ᵥ x0 i) - τ0 • b) ∧
    (∀ i, (A i)ᵀ *ᵥ y1 + s1 i - τ1 • c i
        = (1 - α * (1 - γ)) • ((A i)ᵀ *ᵥ y0 + s0 i - τ0 • c i)) ∧
    -(∑ i, c i ⬝ᵥ x1 i) + b ⬝ᵥ y1 - κ1
        = (1 - α * (1 - γ)) * (-(∑ i, c i ⬝ᵥ x0 i) + b ⬝ᵥ y0 - κ0) ∧
    (∑ i, dx i ⬝ᵥ ds i) + dτ * dκ = 0 ∧
    (∑ i, x1 i ⬝ᵥ s1 i) + τ1 * κ1
        = (1 - α * (1 - γ)) * ((∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0) := by sorry

end ConicQuadIPM.NewtonStep
