-- Prove2me | Theorems.Thm_AdInterm_SPE_lemma_G_1
-- name    : AdInterm.SPE.lemma_G_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:32.530008+00:00
-- url     : https://prove2.me/theorems/1deae0ed-5d26-4d3b-b051-c43e429e6c24
-- title:
--   Lemma G.1, p. 57 — φ_X tends to sup 𝒳, z_X is finite, positive with φ_X(z_X) = 0, and ψ_X is continuous
-- statement:
--   Let $X$ be a nonnegative random variable with cdf $G_X$ and a continuous, strictly positive density $g_X$ on its support $\mathcal X$, whose lower end is $0$. Suppose $\mathbb E[X]<\infty$ and that the virtual value $\phi_X(x)=x-(1-G_X(x))/g_X(x)$ is strictly increasing. Then:
--
--   1. $\displaystyle\lim_{t\to\sup\mathcal X}\phi_X(t)=\sup\mathcal X$ — as a limit from the left when $\sup\mathcal X<\infty$, and $\phi_X(t)\to\infty$ as $t\to\infty$ when the support is unbounded;
--   2. the projection point $z_X=\phi_X^{-1}(0)$ is finite and positive, lies strictly inside the support ($G_X(z_X)<1$), and satisfies
--   $$
--   \phi_X(z_X)=0;
--   $$
--   3. the projected virtual value $\psi_X$ is continuous on $\mathbb R$.
--
--   These facts make $(z_X,\psi_X)$ a well-defined mechanism and are invoked in the proofs of Lemma 3.1 and Theorem 3.1.
--
--   **Formalization Note** $\phi_X$ uses the derivative of the cdf as the density and is considered on the support interval $\{x>0: G_X(x)<1\}$. "Finite" is rendered as $G_X(z_X)<1$, i.e. $z_X$ is strictly below $\sup\mathcal X$. Continuity of $\psi_X$ is asserted on all of $\mathbb R$; below $0$ it is the constant $0$.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), e-companion G, Lemma G.1, p. 57; proof p. 58

import Mathlib
import Definitions.Def_AdInterm_SPE_VirtualValue

open MeasureTheory Filter Topology

namespace AdInterm.SPE

theorem lemma_G_1 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ) :
    ((∃ x, cdf μ x = 1) → Tendsto (phi μ) (𝓝[<] (supX μ)) (𝓝 (supX μ))) ∧
      ((∀ x, cdf μ x < 1) → Tendsto (phi μ) atTop atTop) ∧
      (0 < zproj μ ∧ cdf μ (zproj μ) < 1 ∧ phi μ (zproj μ) = 0) ∧
      Continuous (psi μ) := by sorry

end AdInterm.SPE
