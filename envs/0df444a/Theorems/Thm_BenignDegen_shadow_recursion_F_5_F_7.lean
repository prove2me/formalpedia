-- Prove2me | Theorems.Thm_BenignDegen_shadow_recursion_F_5_F_7
-- name    : BenignDegen.shadow_recursion_F_5_F_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:23.569743+00:00
-- url     : https://prove2.me/theorems/2a42856a-2b6e-45af-9f50-f84bc6ad2a69
-- title:
--   (F.5)–(F.7) — exact ADMM and exact sGS–ADMM share the shadow recursion $Z^{k+1}=T_{\sigma,\tau}(Z^k)$; (5.1)
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Fix $\sigma>0$, $0<\tau<2$, and let $Z^k=\mathsf P^\perp X^k+X_b-\sigma\mathsf PS^k-\sigma\mathsf P^\perp C$ be the shadow of a run.
--
--   1. Along every run of exact ADMM (F.2)–(F.4): $S^{k+1}=-\sigma^{-1}\Pi_-(Z^k)$ (F.5), $X^{k+1}=(1-\tau)X^k+\tau\Pi_+(Z^k)$ (F.6), and $Z^{k+1}=T_{\sigma,\tau}(Z^k)$.
--   2. Along every run of exact sGS–ADMM: (F.5), $X^{k+1}=(\mathrm{Id}-\tau\mathsf P)X^k+\tau X_b+\tau\sigma\mathsf P^\perp(S^{k+1}-C)$ (F.7), and $Z^{k+1}=T_{\sigma,\tau}(Z^k)$.
--   3. For every $Z$, with $\delta_{\sigma,\tau}=T_{\sigma,\tau}-\mathrm{Id}$,
--   $$\|\delta_{\sigma,\tau}(Z)\|_F\ \ge\ \min\{1,\tau\}\,\|\delta_\sigma(Z)\|_F .$$
--
--   Hence both methods are the iteration of one shadow map, and the multiplier step only rescales the two orthogonal residual components.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: the iterates of an algorithm from an arbitrary initialization → every sequence satisfying the update equations for all k (the unused λ⁰ is free); reason: the same runs, quantified universally
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix F.2, (F.2)–(F.7), pp.28–29; §5, (5.1), p.10

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Appendix F.2, (F.5)–(F.7), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, pp.28–29, and (5.1), p.10.
For `σ > 0` and `0 < τ < 2`, along every run of exact ADMM, `S^{k+1} = −σ^{-1}Π₋(Z^k)` (F.5),
`X^{k+1} = (1 − τ)X^k + τΠ₊(Z^k)` (F.6) and `Z^{k+1} = T_{σ,τ}(Z^k)`; along every run of exact
sGS–ADMM, (F.5), `X^{k+1} = (Id − τP)X^k + τX_b + τσP^⊥(S^{k+1} − C)` (F.7) and
`Z^{k+1} = T_{σ,τ}(Z^k)`, with the shadow `Z^k = P^⊥X^k + X_b − σPS^k − σP^⊥C`. Moreover
`‖δ_{σ,τ}(Z)‖_F ≥ min{1, τ}‖δ_σ(Z)‖_F` for every `Z` (the first inequality of (5.1)). -/
theorem shadow_recursion_F_5_F_7 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) (hτ2 : τ < 2) :
    (∀ (X S : ℕ → SymMat ι) (lam : ℕ → EuclideanSpace ℝ κ), D.IsADMMRun σ τ X S lam → ∀ k,
      S (k + 1) = -σ⁻¹ • PiMinus (D.shadow σ X S k) ∧
      X (k + 1) = (1 - τ) • X k + τ • PiPlus (D.shadow σ X S k) ∧
      D.shadow σ X S (k + 1) = D.T σ τ (D.shadow σ X S k)) ∧
    (∀ (X S : ℕ → SymMat ι) (lamH lam : ℕ → EuclideanSpace ℝ κ),
      D.IsSGSRun σ τ X S lamH lam → ∀ k,
      S (k + 1) = -σ⁻¹ • PiMinus (D.shadow σ X S k) ∧
      X (k + 1) = X k - τ • D.P (X k) + τ • D.Xb + (τ * σ) • D.Pperp (S (k + 1) - D.C) ∧
      D.shadow σ X S (k + 1) = D.T σ τ (D.shadow σ X S k)) ∧
    ∀ Z : SymMat ι, min 1 τ * ‖D.delta σ Z‖ ≤ ‖D.deltaTau σ τ Z‖ := by sorry

end BenignDegen
