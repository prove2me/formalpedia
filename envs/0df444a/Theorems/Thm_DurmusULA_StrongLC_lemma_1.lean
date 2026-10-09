-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_lemma_1
-- name    : DurmusULA.StrongLC.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:26.431649+00:00
-- url     : https://prove2.me/theorems/06463a09-152a-4e7b-a668-35ebb1624adb
-- title:
--   Lemma 1, p. 5 — a drift R_γV ≤ λ^γV + γc gives Q^n_γV(x) ≤ F(λ, Γ_n, c, γ_1, V(x))
-- statement:
--   Let $U:\mathbb R^d\to\mathbb R$ satisfy L1 with gradient Lipschitz constant $L$, and let $V:\mathbb R^d\to[0,\infty)$ be Borel. Let $\bar\gamma>0$, $\lambda\in(0,1)$, $c>0$, and assume that for all $x\in\mathbb R^d$ and $\gamma\in(0,\bar\gamma]$ the Euler kernel $R_\gamma$ of $U$ satisfies the drift condition (6):
--   $$R_\gamma V(x)\le\lambda^\gamma V(x)+\gamma c .$$
--   Let $(\gamma_k)_{k\ge1}$ be nonincreasing with $\gamma_k\in(0,\bar\gamma]$ for all $k\ge1$, and $\Gamma_n=\sum_{k=1}^n\gamma_k$. Then for all $n\ge0$ and $x\in\mathbb R^d$,
--   $$Q^n_\gamma V(x)\le F(\lambda,\Gamma_n,c,\gamma_1,V(x)),\qquad F(\lambda,a,c,\gamma,w)=\lambda^aw+c(-\lambda^\gamma\log\lambda)^{-1}.$$
--
--   In particular $\sup_kQ^k_\gamma V(x)\le G(\lambda,c,\gamma_1,V(x))=V(x)+c(-\lambda^{\gamma_1}\log\lambda)^{-1}$ (8). This is how moments of the time-inhomogeneous chain are controlled.
--
--   **Formalization Note** L1 is the standing assumption introduced at the start of §2; it also makes the Euler transition family measurable in its starting point. The paper defines (6) for $V$ with values in $[1,\infty)$, but Theorem 21 applies Lemma 1 to $V(x)=\|x-x^\star\|^2$, which vanishes at $x^\star$; the proof never uses $V\ge1$, so the statement is made for Borel $V\ge0$ (a generalisation). $Q^n_\gamma V(x)$ and $R_\gamma V(x)$ are lower Lebesgue integrals against $\delta_xQ^n_\gamma$ and $R_\gamma(x,\cdot)$.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 5, Lemma 1 and (7); (6) p. 4

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem lemma_1 (d : ℕ) (U V : EthierKurtz.SDEState d → ℝ) (L : ℝ)
    (hL1 : L1 U L) (hVm : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) (γbar lam c : ℝ) (hγbar : 0 < γbar) (hlam : lam ∈ Set.Ioo 0 1)
    (hc : 0 < c)
    (hdrift : ∀ γ : ℝ, 0 < γ → γ ≤ γbar → ∀ x,
      ∫⁻ y, ENNReal.ofReal (V y) ∂(eulerStep U γ x) ≤ ENNReal.ofReal (lam ^ γ * V x + γ * c))
    (γ : ℕ → ℝ) (hγ : ∀ k, 1 ≤ k → 0 < γ k ∧ γ k ≤ γbar)
    (hγmono : ∀ k, 1 ≤ k → γ (k + 1) ≤ γ k) :
    ∀ (n : ℕ) (x : EthierKurtz.SDEState d),
      ∫⁻ y, ENNReal.ofReal (V y) ∂(ulaLaw U γ x n) ≤
        ENNReal.ofReal (F lam (Gam γ 1 n) c (γ 1) (V x)) := by sorry

end DurmusULA.StrongLC
