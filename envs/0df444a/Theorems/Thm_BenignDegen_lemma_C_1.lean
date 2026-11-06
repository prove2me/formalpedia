-- Prove2me | Theorems.Thm_BenignDegen_lemma_C_1
-- name    : BenignDegen.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:11.898102+00:00
-- url     : https://prove2.me/theorems/201930ca-856e-4942-8f6b-bd36b3cb255b
-- title:
--   Lemma C.1 — $T_{\sigma,1}$ is the Douglas–Rachford map, and its fixed points are $X-\sigma S$ over KKT pairs
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Fix $\sigma>0$, let $F(X)=\langle C,X\rangle+\iota_{\{\mathcal AX=b\}}(X)$ and $G=\iota_{\mathbb S^p_+}$. Then $\operatorname{prox}_{\sigma F}$ is well defined, $\Pi_+=\operatorname{prox}_{\sigma G}$ (the unique nearest PSD matrix), and
--
--   $$
--   T_{\sigma,1}(Z)=Z+\operatorname{prox}_{\sigma F}(2\Pi_+(Z)-Z)-\Pi_+(Z).
--   $$
--
--   Its fixed points are exactly the matrices $X-\sigma S$ with $(X,S)$ a KKT pair, decoded via $X=\Pi_+(Z)$, $S=-\sigma^{-1}\Pi_-(Z)$. This identifies the endpoint set $\mathcal Z_\star$ with the KKT pairs.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: prox_{σF}(W) = argmin_X F(X) + ‖X − W‖²/(2σ); T_{σ,1} = Id + δ_σ → a predicate IsProxF with ∃! and the DR identity for the prox point; T σ 1 = Id − D₁(r^∥ + r^⊥_σ); reason: the same objects; T σ 1 = Id + δ_σ is proved in the sanity file
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix C.1, Lemma C.1, p.16

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma C.1 (DR and KKT encoding), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.16.
For `σ > 0`, `prox_{σF}` of `F(X) = ⟨C, X⟩ + ι_{AX=b}(X)` is well defined, `Π₊ = prox_{σG}` for
`G = ι_{S^p_+}` (the unique nearest PSD matrix), `T_{σ,1}` is the Douglas–Rachford map
`Z ↦ Z + prox_{σF}(2Π₊(Z) − Z) − Π₊(Z)`, and its fixed points are exactly the matrices `X − σS`
with `(X, S)` a KKT pair, decoded via `X = Π₊(Z)`, `S = −σ^{-1}Π₋(Z)`. -/
theorem lemma_C_1 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (σ : ℝ) (hσ : 0 < σ) :
    (∀ W : SymMat ι, ∃! X, D.IsProxF σ W X) ∧
    (∀ W : SymMat ι, PiPlus W ∈ psdCone ι ∧
      ∀ Y ∈ psdCone ι, ‖PiPlus W - W‖ ≤ ‖Y - W‖ ∧ (‖Y - W‖ ≤ ‖PiPlus W - W‖ → Y = PiPlus W)) ∧
    (∀ Z X : SymMat ι, D.IsProxF σ ((2 : ℝ) • PiPlus Z - Z) X →
      D.T σ 1 Z = Z + X - PiPlus Z) ∧
    D.Zstar σ = {Z | ∃ X S, D.IsKKT X S ∧ Z = X - σ • S} ∧
    (∀ Z ∈ D.Zstar σ, D.IsKKT (PiPlus Z) (-σ⁻¹ • PiMinus Z)) ∧
    (∀ X S : SymMat ι, D.IsKKT X S →
      PiPlus (X - σ • S) = X ∧ -σ⁻¹ • PiMinus (X - σ • S) = S) := by sorry

end BenignDegen
