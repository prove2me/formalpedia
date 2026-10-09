-- Prove2me | Theorems.Thm_DistCov_Indep_eq_3_4
-- name    : DistCov.Indep.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:11.224892+00:00
-- url     : https://prove2.me/theorems/a5e6f42b-737f-4669-a2a0-911e9ca86c42
-- title:
--   (3.4), p. 11 — D(µ) = −2‖β(µ)‖² when µ(X) = 0
-- statement:
--   Let $\mathcal X$ be a separable metric space with its Borel $\sigma$-field, $H$ a real Hilbert space, and $\phi:\mathcal X\to H$ an embedding, i.e. $d(x,x')=\|\phi(x)-\phi(x')\|^2$ for all $x,x'$. Let $m_1,m_2$ be finite measures on $\mathcal X$ with finite first moments and equal total mass, $m_1(\mathcal X)=m_2(\mathcal X)$, and put $\mu=m_1-m_2$, a signed measure with $\mu(\mathcal X)=0$. Then
--   $$D(\mu)=-2\,\|\beta_\phi(\mu)\|^2,\qquad\text{i.e.}\qquad D(m_1-m_2)=-2\,\big\|\beta_\phi(m_1)-\beta_\phi(m_2)\big\|^2,$$
--   where $\beta_\phi(m)=\int\phi\,dm$ is the barycenter.
--
--   Identity (3.4) converts the energy $D$ of a mass-zero signed measure into a squared Hilbert norm; it shows at once that negative type gives $D(\mu_1-\mu_2)\le0$ and is the key step to Proposition 3.1.
--
--   **Formalization Note** Every finite signed measure $\mu$ with $\mu(\mathcal X)=0$ whose variation has finite first moment is $m_1-m_2$ for its Jordan parts, which have equal mass and finite first moments, so the statement for pairs is (3.4) itself; $D(m_1-m_2)$ is the bilinear expansion `Ddiff`, and $\beta_\phi(m_1-m_2)=\beta_\phi(m_1)-\beta_\phi(m_2)$ by linearity. The integral defining $\beta_\phi$ is genuine: $\phi$ is continuous ($\|\phi(x)-\phi(x')\|=d(x,x')^{1/2}$), hence strongly measurable on the separable space, and $\|\phi(x)\|\le\|\phi(o)\|+1+d(o,x)$ is integrable. Separability is the standing assumption of Errata (i), p. 24.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 11, display (3.4) and the sentence before it; Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem eq_3_4 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (m₁ m₂ : Measure X) [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (h₁ : FiniteFirstMoment m₁) (h₂ : FiniteFirstMoment m₂) (hmass : m₁ Set.univ = m₂ Set.univ) :
    Ddiff m₁ m₂ = -2 * ‖bary ϕ m₁ - bary ϕ m₂‖ ^ 2 := by sorry

end DistCov.Indep
