-- Prove2me | Theorems.Thm_BenignDegen_proposition_F_4
-- name    : BenignDegen.proposition_F_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:56.870659+00:00
-- url     : https://prove2.me/theorems/7ad45afc-fc3d-4031-b46c-0f66c44dc0e9
-- title:
--   Proposition F.4 — PDHG is firmly nonexpansive in $\mathsf G_P$, with $g^P_{\min}=(1-\theta)/\max\{\eta_x,\eta_y\}$, $g^P_{\max}=(1+\theta)/\min\{\eta_x,\eta_y\}$
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Let $\eta_x,\eta_y>0$ with $\theta:=\sqrt{\eta_x\eta_y}\,\|\mathcal A\|_{\rm op}<1$. Then
--
--   $$
--   \mathsf G_P:=\begin{bmatrix}\eta_x^{-1}\mathrm{Id}&\mathcal A^*\\ \mathcal A&\eta_y^{-1}I_m\end{bmatrix}\succ0,
--   $$
--
--   the PDHG map $T_P$ is firmly nonexpansive in $\mathsf G_P$, and for every $w$
--
--   $$
--   \frac{1-\theta}{\max\{\eta_x,\eta_y\}}\|w\|^2\le\|w\|_{\mathsf G_P}^2\le\frac{1+\theta}{\min\{\eta_x,\eta_y\}}\|w\|^2 ,
--   $$
--
--   so these constants may be taken as $g^P_{\min}$, $g^P_{\max}$ in Lemma F.1.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: G_P ≻ 0; 'one may take g^P_min, g^P_max in Lemma F.1' → ⟨w, G_P w⟩ > 0 for w ≠ 0; the two-sided bound on ⟨w, G_P w⟩; reason: the same content: these bounds are exactly the hypothesis of Lemma F.1
--   - encoding: ‖A‖_op → the operator norm of A : (S^p, ‖·‖_F) → (ℝ^m, ‖·‖₂); reason: the same norm
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix F.4, Proposition F.4, p.30

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Proposition F.4 (PDHG parameter-dependent metric), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.30.
If `θ := √(η_xη_y)‖A‖_op < 1`, then `G_P = [[η_x^{-1}Id, A^*], [A, η_y^{-1}I_m]] ≻ 0`, `T_P` is
firmly nonexpansive in `G_P`, and one may take `g^P_min = (1 − θ)/max{η_x, η_y}` and
`g^P_max = (1 + θ)/min{η_x, η_y}` in Lemma F.1. -/
theorem proposition_F_4 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy)
    (hθ : Real.sqrt (ηx * ηy) * ‖D.A‖ < 1) :
    (∀ w : PDSpace ι κ, w ≠ 0 → 0 < gSq (D.GP ηx ηy) w) ∧
    IsFirmlyNonexpansiveIn (D.GP ηx ηy) (D.pdhgMap ηx ηy) ∧
    ∀ w : PDSpace ι κ,
      (1 - Real.sqrt (ηx * ηy) * ‖D.A‖) / max ηx ηy * ‖w‖ ^ 2 ≤ gSq (D.GP ηx ηy) w ∧
      gSq (D.GP ηx ηy) w ≤ (1 + Real.sqrt (ηx * ηy) * ‖D.A‖) / min ηx ηy * ‖w‖ ^ 2 := by sorry

end BenignDegen
