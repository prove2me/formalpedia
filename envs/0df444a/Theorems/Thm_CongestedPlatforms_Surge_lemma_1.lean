-- Prove2me | Theorems.Thm_CongestedPlatforms_Surge_lemma_1
-- name    : CongestedPlatforms.Surge.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:22.675279+00:00
-- url     : https://prove2.me/theorems/de9eb4ea-c00a-46b3-a640-e8039fd339ed
-- title:
--   Lemma 1, p. 15 — the balanced demand and supply of each platform in Case P and Case F (4.2)–(4.7)
-- statement:
--   Fix $\lambda>0$, $\gamma>0$, $\alpha\in(0,1]$, $c\ge0$ and prices $p_0,p_1<1$ with positive driver margins $x_i=\alpha p_i-c>0$. Demands $d_i$ and supplies $s_i$ are **balanced** when they reproduce themselves through the utilization $\rho_i=d_i/s_i$: drivers enter until $s_i=(\alpha p_i-c)\rho_i$ (3.5), and customers choose according to (3.1).
--
--   1. **Case P** (partially covered market). The positive solutions of
--   $$d_0=\lambda(1-p_0-\gamma\rho_0^2),\quad d_1=\lambda(1-p_1-\gamma\rho_1^2),\quad s_i=(\alpha p_i-c)\rho_i\quad(i=0,1)$$
--   — displays (3.2a), (3.2b), (3.5) — are exactly $d_i=d^P_i(p_i)$, $s_i=s^P_i(p_i)$ of (4.3), (4.6).
--   2. At this solution, the location $\underline v_d=1-p_0-\gamma\rho_0^2$ of the customer indifferent between platform 0 and the outside option and the location $\bar v_d=p_1+\gamma\rho_1^2$ of the one indifferent between platform 1 and the outside option satisfy
--   $$\underline v_d\le\bar v_d\iff d^P_0(p_0)+d^P_1(p_1)\le\lambda,$$
--   which is the Case P condition of (4.2), (4.5).
--   3. **Case F** (fully covered market). The positive solutions of
--   $$d_0=\tfrac12\lambda[1-p_0+p_1-\gamma(\rho_0^2-\rho_1^2)],\quad d_1=\tfrac12\lambda[1-p_1+p_0-\gamma(\rho_1^2-\rho_0^2)],\quad s_i=(\alpha p_i-c)\rho_i$$
--   — displays (3.3a), (3.3b), (3.5) — are exactly $d_0=d^F_0(p_0,p_1)$, $d_1=d^F_1(p_1,p_0)$, $s_0=s^F_0(p_0,p_1)$, $s_1=s^F_1(p_1,p_0)$ of (4.4), (4.7).
--
--   This is what justifies the closed forms of balanced demand $D_i$ and supply $S_i$ used throughout the mission: they are the fixed points of the two congestion feedback loops.
--
--   **Formalization Note** $\rho_i$ is written out as $d_i/s_i$. The hypotheses $\alpha p_i-c>0$ and $p_i<1$ describe where the utilization is defined and demand is positive.
--
--   Differences from the source:
--   - reading: "the balanced demand … is given by (4.2) … the corresponding balanced supply … by (4.5)" → in each case the closed forms are the unique positive solution of the balance system (3.2)/(3.3) with (3.5) and $\rho_i=d_i/s_i$, and the Case P solution satisfies $\underline v_d\le\bar v_d$ iff $d^P_0+d^P_1\le\lambda$; reason: this is what the proof (Online Supplement p. 1) establishes; $D_i$, $S_i$ themselves are defined by (4.2)–(4.7) in the Setting.
--   - encoding: prices in $[\underline p,\bar p]$ → $\alpha p_i-c>0$ and $p_i<1$; reason: excludes only the endpoints where demand or supply vanish and $\rho_i=d_i/s_i$ is undefined.
-- source:
--   Bernstein, DeCroix, Keskin, Competition between Two-Sided Platforms under Demand and Supply Congestion Effects, SSRN 3250224, version of September 16, 2019, p. 15, Lemma 1, (4.2)–(4.7); systems (3.2a)–(3.3b), (3.5), pp. 11–13; proof: Online Supplement, p. 1 (PDF 33)

import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem lemma_1 (lam γ α c p0 p1 : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (hx0 : 0 < α * p0 - c) (hx1 : 0 < α * p1 - c) (hp0 : p0 < 1) (hp1 : p1 < 1) :
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = lam * (1 - p0 - γ * (d0 / s0) ^ 2) ∧ d1 = lam * (1 - p1 - γ * (d1 / s1) ^ 2) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dP lam γ α c p0 ∧ d1 = dP lam γ α c p1 ∧
          s0 = sP lam γ α c p0 ∧ s1 = sP lam γ α c p1))) ∧
    (1 - p0 - γ * (dP lam γ α c p0 / sP lam γ α c p0) ^ 2 ≤
        p1 + γ * (dP lam γ α c p1 / sP lam γ α c p1) ^ 2 ↔
      dP lam γ α c p0 + dP lam γ α c p1 ≤ lam) ∧
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = 1 / 2 * lam * (1 - p0 + p1 - γ * ((d0 / s0) ^ 2 - (d1 / s1) ^ 2)) ∧
          d1 = 1 / 2 * lam * (1 - p1 + p0 - γ * ((d1 / s1) ^ 2 - (d0 / s0) ^ 2)) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dF lam γ α c p0 p1 ∧ d1 = dF lam γ α c p1 p0 ∧
          s0 = sF lam γ α c p0 p1 ∧ s1 = sF lam γ α c p1 p0))) := by sorry

end CongestedPlatforms.Surge
