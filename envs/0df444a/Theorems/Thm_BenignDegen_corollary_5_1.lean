-- Prove2me | Theorems.Thm_BenignDegen_corollary_5_1
-- name    : BenignDegen.corollary_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:03.943683+00:00
-- url     : https://prove2.me/theorems/9488636c-aa0f-4a4e-83b8-77c375ed44b6
-- title:
--   Corollary 5.1 — ADMM and sGS–ADMM converge eventually linearly under Assumption 3.1 and the error bound (3.9)
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds and the canonical residual satisfies the setwise error bound (3.9) at $\sigma>0$ (equivalently, by Theorem 3.2, any of the conditions (i)–(v)). Then for every $0<\tau<2$, along every run of exact ADMM and every run of exact sGS–ADMM:
--
--   1. the shadow $Z^k$ converges to an endpoint $\bar Z\in\mathcal Z_\star$;
--   2. $\operatorname{dist}_{\mathsf G_\tau}(Z^k,\mathcal Z_\star)$ contracts eventually Q-linearly;
--   3. the shadow and the raw primal–dual iterates $X^k$, $S^k$, $\lambda^k$ converge R-linearly, the limits forming a KKT triple $(\bar X,\bar\lambda,\bar S)$ with $\bar Z=\bar X-\sigma\bar S$.
--
--   The convergence is eventual: it begins after an entrance time that is not bounded.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: R-linear convergence, eventual Q-linear contraction → RLinearTo (‖u_k − ū‖ ≤ cρ^k for all k, 0 ≤ ρ < 1), EventuallyQLinear (d_{k+1} ≤ ρ d_k for all k ≥ K, 0 ≤ ρ < 1); reason: the standard definitions; ρ < 1 is strict
--   - encoding: the iterates of an algorithm from an arbitrary initialization → every sequence satisfying the update equations for all k (the unused λ⁰ is free); reason: the same runs, quantified universally
--   - generalization: the limits are an endpoint Z̄ and R-linear limits of the raw iterates → also states that the limits (X̄, λ̄, S̄) form a KKT triple with Z̄ = X̄ − σS̄; reason: shown in the proof (Appendix F.3, p.29: X̄, S̄ are the factors of Z̄ and λ̄ the unique multiplier of S̄); dropping the clause gives the source's statement
--   - encoding: Assumption 3.1 plus any condition of Theorem 3.2 → Assumption 3.1 plus condition (iii), the error bound (3.9); reason: the conditions are equivalent under Assumption 3.1 (Theorem 3.2)
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §5, Corollary 5.1, pp.10–11; proof in Appendix F.3, p.29

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Corollary 5.1 (ADMM and sGS–ADMM), abstract form, Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, pp.10–11.
Under Assumption 3.1 plus condition (iii) of Theorem 3.2 (the error bound (3.9)), for every fixed
`σ > 0` and `0 < τ < 2`, the shadow orbits of exact ADMM and exact sGS–ADMM converge to an
endpoint of `Z_⋆`, the distance contracts eventually Q-linearly in the `G_τ` metric, and the
shadow and the raw primal–dual iterates converge R-linearly (to a KKT triple whose endpoint is
the limit of the shadow). -/
theorem corollary_5_1 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (σ : ℝ)
    (hσ : 0 < σ) (heb : D.ErrorBound σ) (τ : ℝ) (hτ : 0 < τ) (hτ2 : τ < 2) :
    (∀ (X S : ℕ → SymMat ι) (lam : ℕ → EuclideanSpace ℝ κ),
      D.IsADMMRun σ τ X S lam → D.ADMMConclusions σ τ X S lam) ∧
    (∀ (X S : ℕ → SymMat ι) (lamH lam : ℕ → EuclideanSpace ℝ κ),
      D.IsSGSRun σ τ X S lamH lam → D.ADMMConclusions σ τ X S lam) := by sorry

end BenignDegen
