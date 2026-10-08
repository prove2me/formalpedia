-- Prove2me | Theorems.Thm_BoydADMM_Prox_softThreshold_eq_posPart
-- name    : BoydADMM.Prox.softThreshold_eq_posPart
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:48.448985+00:00
-- url     : https://prove2.me/theorems/8e6d10d9-208c-4947-8924-4852593122fb
-- title:
--   §4.4.3, p. 32 — S_κ(a) = (a − κ)₊ − (−a − κ)₊
-- statement:
--   For $\kappa\ge0$ and every $a\in\mathbb R$, the soft thresholding operator
--   $$S_\kappa(a)=\begin{cases}a-\kappa & a>\kappa\\ 0 & |a|\le\kappa\\ a+\kappa & a<-\kappa\end{cases}$$
--   satisfies
--   $$S_\kappa(a)=(a-\kappa)_+-(-a-\kappa)_+,$$
--   where $(t)_+=\max(t,0)$.
--
--   This is the "equivalently" form of soft thresholding, written without cases.
--
--   **Formalization Note** The book leaves $\kappa\ge0$ implicit (it uses $\kappa=\lambda/\rho$ with $\lambda,\rho>0$); for $\kappa<0$ the identity fails (e.g. $\kappa=-1$, $a=0$), so the hypothesis is stated.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 32, §4.4.3

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem softThreshold_eq_posPart (κ : ℝ) (hκ : 0 ≤ κ) (a : ℝ) :
    softThreshold κ a = max (a - κ) 0 - max (-a - κ) 0 := by sorry

end BoydADMM.Prox
