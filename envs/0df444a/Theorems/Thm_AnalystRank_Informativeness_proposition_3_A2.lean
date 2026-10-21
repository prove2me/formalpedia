-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_proposition_3_A2
-- name    : AnalystRank.Informativeness.proposition_3_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:06.741985+00:00
-- url     : https://prove2.me/theorems/d6637792-6056-4f0d-9766-af20ecae51fe
-- title:
--   Proposition 3 (A.2, corrected) — high convexity and correlation: (σ̇ʰ, σ̇ˡ) on [1 − q̄, q̄], (1, σ̌ˡ(q)) on (q̄, q̌max), pooling beyond
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\le1$, and $w_1>w_0>w_2$ with $\varphi>1$, in the regime of high correlation and high convexity: $\rho>\bar\rho$ and $\varphi>\bar\varphi$. Let $\ddot\sigma^l\in(0,1)$ be the crossing point of Claim 3 (B.2), $\bar q=\frac{g_l(1,\ddot\sigma^l)}{1+g_l(1,\ddot\sigma^l)}$ as in (B.33), and $\dot\sigma^h,\dot\sigma^l$ the fully mixed strategies (B.34). For every prior $q\in(0,1)$ the rank game has a most informative equilibrium $\sigma$, and:
--
--   1. $\dot\sigma^h(q),\dot\sigma^l(q)\in(0,1]$, with $\dot\sigma^h(q)<1$ for $q<\bar q$ and $\dot\sigma^l(q)<1$ for $q>1-\bar q$, and $\sigma=(\dot\sigma^h(q),\dot\sigma^l(q))$ if $q\in[1-\bar q,\bar q]$;
--   2. $\check\sigma^h(q)\in(0,\ddot\sigma^h)$ and $\sigma=(\check\sigma^h(q),1)$ if $q\in(1-\check q_{\max},1-\bar q)$; $\check\sigma^l(q)\in(0,\ddot\sigma^l)$ and $\sigma=(1,\check\sigma^l(q))$ if $q\in(\bar q,\check q_{\max})$;
--   3. $\sigma^h=1-\sigma^l$ (pooling) if $q\in(0,1-\check q_{\max}]\cup[\check q_{\max},1)$.
--
--   Here no separating equilibrium exists at any prior. Around $q=\tfrac12$ both analysts randomize after either signal. This is the existence half of the goal in this regime.
--
--   **Formalization Note** *Corrected:* the printed condition is $\varphi\ge\bar\varphi$. At $\varphi=\bar\varphi$, $\check q_{\min}=\tfrac12$, so $(1,1)$ is an equilibrium at $q=\tfrac12$, and $g_l(1,\cdot)=g_h(1,\cdot)$ only at $\sigma^l=1$. That boundary is covered by Proposition 3 (A.1). The printed open range $(0,1)$ for both coordinates on the closed interval $[1-\bar q,\bar q]$ is also corrected: both coordinates lie in $(0,1)$ on the open interval $(1-\bar q,\bar q)$, while $\dot\sigma^h(\bar q)=1$ and $\dot\sigma^l(1-\bar q)=1$ at the endpoints. The paper never defines $\ddot\sigma^h$; it is taken equal to $\ddot\sigma^l$ by symmetry, which is consistent with $\check\sigma^h(q)=\check\sigma^l(1-q)$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), pp. 15–16, Proposition 3 (A.2); (B.32)–(B.35), (B.42), pp. 46–47, 50 (φ ≥ φ̄ corrected to φ > φ̄; endpoint range (0,1) corrected to (0,1) inside and 1 for one coordinate at each endpoint)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model
import Definitions.Def_AnalystRank_Informativeness_ClosedForms

namespace AnalystRank.Informativeness

open Set

theorem proposition_3_A2 (γ ρ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : 1 < phi w1 w0 w2)
    (hρ : rhoBar γ < ρ) (hφbar : phiBar γ ρ < phi w1 w0 w2) :
    ∀ q ∈ Ioo (0 : ℝ) 1,
      (∃ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ) ∧
      ∀ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ →
        (q ∈ Icc (1 - qBar w1 w0 w2 γ ρ) (qBar w1 w0 w2 γ ρ) →
          sigmaDotH γ ρ (phi w1 w0 w2) q ∈ Ioc (0 : ℝ) 1 ∧
          sigmaDotL γ ρ (phi w1 w0 w2) q ∈ Ioc (0 : ℝ) 1 ∧
          (q < qBar w1 w0 w2 γ ρ → sigmaDotH γ ρ (phi w1 w0 w2) q < 1) ∧
          (1 - qBar w1 w0 w2 γ ρ < q → sigmaDotL γ ρ (phi w1 w0 w2) q < 1) ∧
          σ = (sigmaDotH γ ρ (phi w1 w0 w2) q, sigmaDotL γ ρ (phi w1 w0 w2) q)) ∧
        (q ∈ Ioo (1 - qmaxCheck γ (phi w1 w0 w2)) (1 - qBar w1 w0 w2 γ ρ) →
          sigmaCheckH γ ρ (phi w1 w0 w2) q ∈ Ioo (0 : ℝ) (sigmaDDotL w1 w0 w2 γ ρ) ∧
          σ = (sigmaCheckH γ ρ (phi w1 w0 w2) q, 1)) ∧
        (q ∈ Ioo (qBar w1 w0 w2 γ ρ) (qmaxCheck γ (phi w1 w0 w2)) →
          sigmaCheckL γ ρ (phi w1 w0 w2) q ∈ Ioo (0 : ℝ) (sigmaDDotL w1 w0 w2 γ ρ) ∧
          σ = (1, sigmaCheckL γ ρ (phi w1 w0 w2) q)) ∧
        ((q ≤ 1 - qmaxCheck γ (phi w1 w0 w2) ∨ qmaxCheck γ (phi w1 w0 w2) ≤ q) →
          σ.1 = 1 - σ.2) := by sorry

end AnalystRank.Informativeness
