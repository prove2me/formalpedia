-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_theorem_6
-- name    : DataDrivenRO.FwdBwd.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:02:49.40258+00:00
-- url     : https://prove2.me/theorems/2a39d195-233b-407d-ab71-cf3458fa5df7
-- title:
--   Theorem 6, p. 19 — 𝒰^{FB}_ε is compact convex, δ*(v|𝒰^{FB}_ε) is (24), and (24) ≥ VaR^ℙ_ε(v) for every independent ℙ in 𝒫^{FB}
-- statement:
--   Let $m_b,m_f,\bar\sigma_f,\bar\sigma_b\in\mathbb R^d$ with $m_{bi}\le m_{fi}$, $\bar\sigma_{fi}>0$, $\bar\sigma_{bi}>0$ for all $i$, and let $\varepsilon\in(0,1)$. Let $\mathcal U^{FB}_\varepsilon$ be the set (23) and $F(v)$ the right-hand side of (24),
--   $$F(v) = \sum_{i:v_i\ge0}m_{fi}v_i+\sum_{i:v_i<0}m_{bi}v_i+\sqrt{2\log(1/\varepsilon)\Big(\sum_{i:v_i\ge0}\bar\sigma_{fi}^2v_i^2+\sum_{i:v_i<0}\bar\sigma_{bi}^2v_i^2\Big)}.$$
--   Then:
--
--   1. for every family of probability measures $\mathbb P_1,\dots,\mathbb P_d$ on $\mathbb R$ admissible for $\mathcal P^{FB}$ (bounded support, mean in $[m_{bi},m_{fi}]$, forward deviation at most $\bar\sigma_{fi}$, backward deviation at most $\bar\sigma_{bi}$), the product $\mathbb P=\mathbb P_1\otimes\cdots\otimes\mathbb P_d$ satisfies $\mathrm{VaR}^{\mathbb P}_\varepsilon(v)\le F(v)$ for every $v$;
--   2. $\delta^*(v\mid\mathcal U^{FB}_\varepsilon) = F(v)$ for every $v\in\mathbb R^d$, which is (24);
--   3. $\mathcal U^{FB}_\varepsilon$ is nonempty, convex and compact.
--
--   Together, 1 and 2 say that $\delta^*(v\mid\mathcal U^{FB}_\varepsilon)\ge\mathrm{VaR}^{\mathbb P}_\varepsilon(v)$ for every $v$, every $\varepsilon\in(0,1)$ and every independent $\mathbb P$ in $\mathcal P^{FB}$. By Theorem 1 of the paper this criterion, for a nonempty convex compact set, is the probabilistic guarantee; whenever the true distribution lies in the confidence region, the whole family $\{\mathcal U^{FB}_\varepsilon\}$ implies a probabilistic guarantee for it.
--
--   **Formalization Note** The theorem formalizes the deterministic content of Theorem 6. The page's "with probability $1-\alpha$ with respect to the sample" is the coverage of $\mathcal P^{FB}$ by the true distribution, whose thresholds come from a bootstrap (Algorithm 1) and are only approximately valid; it is not formalized. Independence and bounded support (the theorem's hypotheses on $\mathbb P^*$) are built into the region. $\bar\sigma>0$ is assumed so that the denominators of (23) are genuine (Lean's $x/0=0$ would otherwise leave $y_2$ or $y_3$ unconstrained, whereas the page means $y=0$). $m_b\le m_f$ holds because $m_b=\hat\mu-t$, $m_f=\hat\mu+t$ with $t\ge0$. The support function is a real supremum; conjunct 3 makes it the true maximum.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, (23), (24), p. 19; proof EC.1.4, p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

open MeasureTheory

namespace DataDrivenRO.FwdBwd

theorem theorem_6 {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)], Admissible mb mf sf sb Q →
        ∀ v, VaR (Measure.pi Q) ε v ≤ fbValue mb mf sf sb ε v) ∧
    (∀ v, RobustMDP.Shared.supportFunction (UFB mb mf sf sb ε) v = fbValue mb mf sf sb ε v) ∧
    ((UFB mb mf sf sb ε).Nonempty ∧ Convex ℝ (UFB mb mf sf sb ε) ∧
      IsCompact (UFB mb mf sf sb ε)) := by sorry

end DataDrivenRO.FwdBwd
