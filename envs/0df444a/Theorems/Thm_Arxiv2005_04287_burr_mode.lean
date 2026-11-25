-- Prove2me | Theorems.Thm_Arxiv2005_04287_burr_mode
-- name    : Arxiv2005_04287.burr_mode
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:09:58.802351+00:00
-- url     : https://prove2.me/theorems/c0770b34-8721-472b-8b53-e82e44f01abc
-- title:
--   Eq. (10), p. 8: the peak of the Burr amplitude density is at $A=\lambda/\sqrt{2b-1}$ (as proved, for $b>1$)
-- statement:
--   Let $b>1$ and $\lambda>0$. The Burr amplitude density of eq. (10),
--
--   $$p[A]=\frac{2A(b-1)}{\lambda^2\big[(A/\lambda)^2+1\big]^b}\quad(A>0),\qquad p[A]=0\quad(A\le0),$$
--
--   has its peak at $A=\lambda/\sqrt{2b-1}$: for every real $A\ne\lambda/\sqrt{2b-1}$, $p[A]<p[\lambda/\sqrt{2b-1}]$.
--
--   **Formalization Note** The paper states the peak location for $b>1/2$. For $1/2<b<1$ the expression (10) is negative for every $A>0$ (its factor $b-1$ is negative), so $\lambda/\sqrt{2b-1}$ is its minimum, not its peak, and for $b=1$ it vanishes identically. Eq. (10) is a probability density only for $b>1$, so the statement is made for $b>1$.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c002; Theory, 'Probability of Amplitudes', text after eq. (10), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem burr_mode (b lam : ℝ) (hb : 1 < b) (hlam : 0 < lam) :
    ∀ A : ℝ, A ≠ lam / Real.sqrt (2 * b - 1) →
      burrDensity b lam A < burrDensity b lam (lam / Real.sqrt (2 * b - 1)) := by sorry

end Arxiv2005_04287
