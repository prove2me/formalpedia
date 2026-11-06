-- Prove2me | Theorems.Thm_BenignDegen_corollary_5_2
-- name    : BenignDegen.corollary_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:56.103195+00:00
-- url     : https://prove2.me/theorems/eb585acd-dd93-4424-98b3-86b94c0dd62c
-- title:
--   Corollary 5.2 — PDHG converges eventually linearly to a KKT pair under Assumption 3.1 and (3.9) at $\sigma=\eta_x$
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds, the canonical residual with $\sigma=\eta_x$ satisfies the setwise error bound (3.9), and $\eta_x,\eta_y>0$ with $\eta_x\eta_y\|\mathcal A\|_{\rm op}^2<1$. Then every PDHG orbit $(X^k,\lambda^k)$ converges to a KKT pair $(\bar X,\bar\lambda)\in\mathcal W_\star$; the distance to $\mathcal W_\star$ contracts eventually Q-linearly in the preconditioned metric $\mathsf G_P$; and the iterates and the slack $S^k=C-\mathcal A^*\lambda^k$ converge R-linearly.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: R-linear convergence, eventual Q-linear contraction → RLinearTo (‖u_k − ū‖ ≤ cρ^k for all k, 0 ≤ ρ < 1), EventuallyQLinear (d_{k+1} ≤ ρ d_k for all k ≥ K, 0 ≤ ρ < 1); reason: the standard definitions; ρ < 1 is strict
--   - encoding: the iterates of an algorithm from an arbitrary initialization → every sequence satisfying the update equations for all k (the unused λ⁰ is free); reason: the same runs, quantified universally
--   - encoding: 'under the same hypotheses' (Assumption 3.1 plus any condition of Theorem 3.2) → Assumption 3.1 plus condition (iii) at σ = η_x; reason: the conditions are equivalent under Assumption 3.1 (Theorem 3.2)
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §5, Corollary 5.2, p.11; proof p.30

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Corollary 5.2 (PDHG), abstract form, Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.11.
Under Assumption 3.1 and condition (iii) of Theorem 3.2 with `σ = η_x`, and
`η_xη_y‖A‖²_op < 1`, every PDHG orbit converges to a KKT pair; the distance to `W_⋆` contracts
eventually Q-linearly in the preconditioned metric `G_P`, and the iterates and the slack
`S^k = C − A^*λ^k` converge R-linearly. -/
theorem corollary_5_2 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (ηx ηy : ℝ)
    (hηx : 0 < ηx) (hηy : 0 < ηy) (heb : D.ErrorBound ηx) (hstep : ηx * ηy * ‖D.A‖ ^ 2 < 1) :
    ∀ (X : ℕ → SymMat ι) (lam : ℕ → EuclideanSpace ℝ κ),
      D.IsPDHGRun ηx ηy X lam → D.PDHGConclusions ηx ηy X lam := by sorry

end BenignDegen
