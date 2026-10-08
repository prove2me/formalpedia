-- Prove2me | Theorems.Thm_BoundedNV_ExpFam_observation_exponential_family
-- name    : BoundedNV.ExpFam.observation_exponential_family
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:34.264741+00:00
-- url     : https://prove2.me/theorems/384d4cb3-6a74-4cbf-a529-90c8f3da83e2
-- title:
--   Observation, p. 575 — the newsvendor choice distributions form a two-parameter exponential family
-- statement:
--   Let $D$ have density $f$ (nonnegative, vanishing on $(-\infty,0)$, total mass $1$), let $S$ be the smallest interval containing the support of $f$, let the price $p$ and cost $c$ satisfy $0<c<p$, and let $\beta>0$. Put $\eta_1 = p/\beta$, $\eta_2 = c/\beta$, $T_1(x) = E\min(D,x)$ and $T_2(x) = -x$. Then:
--
--   1. $v\mapsto e^{\eta_1 E\min(D,v)-\eta_2 v}$ is integrable on $S$ and its integral $\int_S e^{\eta_1 E\min(D,v)-\eta_2 v}\,dv$ is strictly positive, so $A(\eta_1,\eta_2)$ of (12) is a genuine logarithm;
--   2. the behavioral solution's density $\psi_{p,c}$ of (11) is a probability density, $\int_{\mathbb R}\psi_{p,c}=1$;
--   3. for every $x$,
--   $$\psi_{p,c}(x) = \mathbf 1_S(x)\,\exp\big\{\eta_1 T_1(x) + \eta_2 T_2(x) - A(\eta_1,\eta_2)\big\},$$
--   which is the exponential-family form (10) with $s=2$ and base factor $l = \mathbf 1_S$.
--
--   This identifies the newsvendor's choice distribution as a member of a two-dimensional exponential family with natural parameters $(p/\beta, c/\beta)$, the structure on which Proposition 2 rests.
--
--   **Formalization Note** The page writes $l(x)\equiv 1$; with the density understood on $S$, as in (11), the base factor is the indicator of $S$. The standing readings $\beta>0$ (eq. (2) divides by $\beta$) and $c>0$ are added; $p>c$ is the paper's. No finite mean of $D$ is assumed: $E\min(D,v)$ grows sublinearly, which with $\eta_2>0$ makes the integral finite even for unbounded $S$. Items 1–2 are stated so that the identity cannot hold through Lean's junk values $\ln 0 = 0$ and $x/0=0$.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 575 (PDF p. 10), Observation, eqs. (10)–(12)

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
import Definitions.Def_BoundedNV_ExpFam_LogPartition

namespace BoundedNV.ExpFam

theorem observation_exponential_family (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (p c β : ℝ) (hβ : 0 < β) (hc : 0 < c) (hcp : c < p) :
    MeasureTheory.IntegrableOn
        (fun v => Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v)) (decisionDomain f) ∧
      0 < ∫ v in decisionDomain f, Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v) ∧
      (∫ x, BoundedNV.Uniform.logitDensity (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β x = 1) ∧
      BoundedNV.Uniform.logitDensity (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β =
        (decisionDomain f).indicator (fun x =>
          Real.exp (p / β * BoundedNV.Uniform.expMin f x + c / β * (-x) - logPartition f (p / β) (c / β))) := by sorry

end BoundedNV.ExpFam
