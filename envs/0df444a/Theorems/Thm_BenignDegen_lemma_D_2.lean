-- Prove2me | Theorems.Thm_BenignDegen_lemma_D_2
-- name    : BenignDegen.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:51.718193+00:00
-- url     : https://prove2.me/theorems/56c62d79-42b1-4c81-8bc3-a035e3f204c1
-- title:
--   Lemma D.2 — uniformly bounded normal decompositions (D.4)
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds with anchor pair $(X_{\rm sc},S_{\rm sc})$, $U=\operatorname{ran}X_{\rm sc}$, $V=\operatorname{ran}S_{\rm sc}$, and fix $\sigma>0$. Let $a_X=\lambda_{\min}(X_{\rm sc}|_U)$, $a_S=\lambda_{\min}(S_{\rm sc}|_V)$, $R_X=\max_{X\in\mathcal X_\star}\|X_{\rm sc}-X\|_F$, $R_S=\max_{S\in\mathcal S_\star}\|S_{\rm sc}-S\|_F$ (D.1). For every endpoint $\bar Z=\bar X-\sigma\bar S$, every $H\in N_{\mathcal Z_\star}(\bar Z)$ and every decomposition $H=Y-W_U+W_V$ with $Y\in\mathcal D^\perp$, $W_U\in\mathcal K(\bar X)$, $W_V\in\mathcal K(\bar S)$ as in (C.10),
--
--   $$
--   \|W_U\|_F\le\frac{R_X}{a_X}\|H\|_F,\qquad \|W_V\|_F\le\frac{R_S}{a_S}\|H\|_F,\qquad \|Y\|_F\le\Bigl(1+\frac{R_X}{a_X}+\frac{R_S}{a_S}\Bigr)\|H\|_F. \tag{D.4}
--   $$
--
--   The three summands need not be orthogonal, and the decomposition need not be unique; the bounds hold for every choice.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: N_C(z), with N_C(z) = ∅ for z ∉ C → published RobinsonSR.Reduction.normalCone; reason: the same set
--   - encoding: S(E) = {H : H = P_E H P_E}, X_UU ≻ 0, P_K M P_K ⪰ 0 → supported E (kernel of H ↦ H − P_E H P_E), PosDefOn E X (⟨v, Xv⟩ > 0 for 0 ≠ v ∈ E), PSDOn K M (⟨v, Mv⟩ ≥ 0 for v ∈ K); reason: basis-free forms of the same conditions
--   - generalization: a_X = λ_min(X_sc|_U), a_S = λ_min(S_sc|_V), R_X, R_S the maxima (D.1) → every a_X, a_S > 0 that bound λ_min from below on U, V and every R_X, R_S that bound the distances from above; reason: the bounds (D.4) are monotone in these constants, and the paper's constants are one admissible choice
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix D.2, (D.1), Lemma D.2, (D.4), pp.20–21

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma D.2 (uniformly bounded normal decompositions), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.21.
Under Assumption 3.1, for every endpoint `Z̄ = X̄ − σS̄`, every `H ∈ N_{Z_⋆}(Z̄)` and every
decomposition `H = Y − W_U + W_V` with `Y ∈ D^⊥`, `W_U ∈ K(X̄)`, `W_V ∈ K(S̄)` as in (C.10),
`‖W_U‖_F ≤ (R_X/a_X)‖H‖_F`, `‖W_V‖_F ≤ (R_S/a_S)‖H‖_F`,
`‖Y‖_F ≤ (1 + R_X/a_X + R_S/a_S)‖H‖_F` (D.4), where `a_X = λ_min(X_sc|_U)`,
`a_S = λ_min(S_sc|_V)` and `R_X = max_{X∈X_⋆}‖X_sc − X‖_F`, `R_S = max_{S∈S_⋆}‖S_sc − S‖_F` (D.1).

**Formalization Note** Stated for every `a_X, a_S > 0` that bound `λ_min(X_sc|_U)`,
`λ_min(S_sc|_V)` from below and every `R_X, R_S` that bound the radii (D.1) from above; the
paper's constants are one such choice, and the bounds (D.4) are monotone in these constants. -/
theorem lemma_D_2 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (σ : ℝ) (hσ : 0 < σ)
    (aX aS RX RS : ℝ) (haX : 0 < aX) (haS : 0 < aS)
    (hXsc : ∀ u ∈ ranSub Xsc, aX * ‖u‖ ^ 2 ≤ ⟪u, act Xsc u⟫)
    (hSsc : ∀ v ∈ ranSub Ssc, aS * ‖v‖ ^ 2 ≤ ⟪v, act Ssc v⟫)
    (hRX : ∀ X ∈ D.Xstar, ‖Xsc - X‖ ≤ RX) (hRS : ∀ S ∈ D.Sstar, ‖Ssc - S‖ ≤ RS)
    (Xbar Sbar : SymMat ι) (hX : Xbar ∈ D.Xstar) (hS : Sbar ∈ D.Sstar)
    (H : SymMat ι) (hH : H ∈ RobinsonSR.Reduction.normalCone (D.Zstar σ) (Xbar - σ • Sbar))
    (Y WU WV : SymMat ι) (hY : Y ∈ (D.Ddir Xsc Ssc)ᗮ)
    (hWU : WU ∈ kerCone (kerSub Xbar ⊓ ranSub Xsc)) (hWV : WV ∈ kerCone (kerSub Sbar ⊓ ranSub Ssc))
    (hdec : H = Y - WU + WV) :
    ‖WU‖ ≤ RX / aX * ‖H‖ ∧ ‖WV‖ ≤ RS / aS * ‖H‖ ∧
      ‖Y‖ ≤ (1 + RX / aX + RS / aS) * ‖H‖ := by sorry

end BenignDegen
