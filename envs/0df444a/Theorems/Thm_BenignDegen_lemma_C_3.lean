-- Prove2me | Theorems.Thm_BenignDegen_lemma_C_3
-- name    : BenignDegen.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:54.687017+00:00
-- url     : https://prove2.me/theorems/2b75b1e4-19dd-419b-9633-907f10307ee8
-- title:
--   Lemma C.3 — Sylvester estimates $\|\mathrm{Syl}^{-1}\|_{F\to F}\le a^{-1}$ and $\le(\sigma b)^{-1}$
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds with anchor pair $(X_{\rm sc},S_{\rm sc})$, $U=\operatorname{ran}X_{\rm sc}$, $V=\operatorname{ran}S_{\rm sc}$, and fix $\sigma>0$. Let $\mathrm{Syl}:Y\mapsto AY+\sigma YB$ act on $r\times s$ matrices, $A\succeq0$, $B\succeq0$.
--
--   1. (a) If $A\succeq aI$ with $a>0$, then $\mathrm{Syl}$ is invertible and $\|\mathrm{Syl}^{-1}\|_{F\to F}\le a^{-1}$, uniformly over all $B\succeq0$.
--   2. (b) If $B\succeq bI$ with $b>0$, then $\mathrm{Syl}$ is invertible and $\|\mathrm{Syl}^{-1}\|_{F\to F}\le(\sigma b)^{-1}$, uniformly over all $A\succeq0$.
--   3. In particular, with $a_X=\lambda_{\min}(X_{\rm sc}|_U)$, $a_S=\lambda_{\min}(S_{\rm sc}|_V)$ and blocks taken in orthonormal bases of $U$, $V$: the operators $Y\mapsto X_{\rm sc}|_UY+\sigma Y\bar S_{VV}$ have inverse norm at most $a_X^{-1}$ for every $\bar S\in\mathcal S_\star$, and $Y\mapsto\bar X_{UU}Y+\sigma YS_{\rm sc}|_V$ at most $(\sigma a_S)^{-1}$ for every $\bar X\in\mathcal X_\star$.
--
--   These bounds are uniform over the moving optima: they rest on the anchor pair only.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: ‖Syl^{-1}‖_{F→F} ≤ c^{-1} → Syl bijective and c‖Y‖_F ≤ ‖Syl(Y)‖_F for all Y; reason: equivalent formulations
--   - generalization: A ∈ S₊(U), B ∈ S₊(V) in the fixed bases (sizes dim U × dim V) → any sizes r × s, A, B PSD; reason: the source's case r = dim U, s = dim V is an instance
--   - generalization: a_X = λ_min(X_sc|_U), a_S = λ_min(S_sc|_V), fixed bases B_U, B_V → every a_X > 0 with a_X‖u‖² ≤ ⟨u, X_sc u⟩ on U (resp. a_S on V), every orthonormal bases; reason: λ_min itself is such a lower bound and the fixed bases are one choice
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix C.3, Lemma C.3, p.18

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma C.3 (Sylvester estimates), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.18.
Let `Syl : Y ↦ AY + σYB` act on `r × s` matrices, `A ⪰ 0`, `B ⪰ 0` (in (a), `A ⪰ 0` follows from
`A ⪰ aI`; in (b), `B ⪰ 0` from `B ⪰ bI`).
(a) If `A ⪰ aI` with `a > 0`, `Syl` is invertible and `‖Syl^{-1}‖_{F→F} ≤ a^{-1}`, uniformly over
`B ⪰ 0`. (b) If `B ⪰ bI` with `b > 0`, `Syl` is invertible and `‖Syl^{-1}‖_{F→F} ≤ (σb)^{-1}`,
uniformly over `A ⪰ 0`. In particular (under Assumption 3.1, in fixed orthonormal bases
`B_U`, `B_V`), the Sylvester operators `Y ↦ X_sc|_U Y + σY S̄_VV` have inverse norm at most
`a_X^{-1}` for every `S̄ ∈ S_⋆`, and `Y ↦ X̄_UU Y + σY S_sc|_V` at most `(σa_S)^{-1}` for every
`X̄ ∈ X_⋆`.

**Formalization Note** `‖Syl^{-1}‖_{F→F} ≤ c^{-1}` is stated as "`Syl` is bijective and
`c‖Y‖_F ≤ ‖Syl(Y)‖_F` for all `Y`". The "in particular" part is stated for every `a > 0` with
`a‖u‖² ≤ ⟨u, X_sc u⟩` on `U` (every positive lower bound of `a_X = λ_min(X_sc|_U)`, `a_X` itself
included), and likewise for `a_S`, and for every choice of the orthonormal bases. -/
theorem lemma_C_3 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (σ : ℝ) (hσ : 0 < σ) :
    (∀ (r s : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin s) (Fin s) ℝ) (a : ℝ), 0 < a →
      (A - a • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef → B.PosSemidef →
      Function.Bijective (sylv σ A B) ∧ ∀ Y, a * frob Y ≤ frob (sylv σ A B Y)) ∧
    (∀ (r s : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin s) (Fin s) ℝ) (b : ℝ), 0 < b →
      A.PosSemidef → (B - b • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef →
      Function.Bijective (sylv σ A B) ∧ ∀ Y, σ * b * frob Y ≤ frob (sylv σ A B Y)) ∧
    (∀ (r s : ℕ) (bU : OrthonormalBasis (Fin r) ℝ (ranSub Xsc))
      (bV : OrthonormalBasis (Fin s) ℝ (ranSub Ssc)),
      (∀ aX : ℝ, 0 < aX → (∀ u ∈ ranSub Xsc, aX * ‖u‖ ^ 2 ≤ ⟪u, act Xsc u⟫) →
        ∀ Sbar ∈ D.Sstar, Function.Bijective (sylv σ (blk bU bU Xsc) (blk bV bV Sbar)) ∧
          ∀ Y, aX * frob Y ≤ frob (sylv σ (blk bU bU Xsc) (blk bV bV Sbar) Y)) ∧
      (∀ aS : ℝ, 0 < aS → (∀ v ∈ ranSub Ssc, aS * ‖v‖ ^ 2 ≤ ⟪v, act Ssc v⟫) →
        ∀ Xbar ∈ D.Xstar, Function.Bijective (sylv σ (blk bU bU Xbar) (blk bV bV Ssc)) ∧
          ∀ Y, σ * aS * frob Y ≤ frob (sylv σ (blk bU bU Xbar) (blk bV bV Ssc) Y))) := by sorry

end BenignDegen
