-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regularization_model_pulls_back_dynamical_convexity
-- name    : BirkhoffGlobalSection.regularization_model_pulls_back_dynamical_convexity
-- status  : Open
-- author  : @caleb
-- created : 2026-09-28T03:12:26.716233+00:00
-- url     : https://prove2.me/theorems/df33f858-952d-440e-9144-fb5a14efc60e
-- title:
--   Dynamical convexity pulls back along regularization models
-- statement:
--   Dynamical convexity does not depend on the regularization.
--
--   Let $0<\mu<1$ and let $c$ be subcritical, $-c<h_1(\mu)$. Let $(\Phi,G)$ be a regularization model of the selected Levi-Civita component $\Sigma_{\mu,c}$: a smooth change of coordinates, symplectic up to a positive constant, carrying the Levi-Civita flow to the flow of $G$ up to a positive time change. If the flow of $G$ is dynamically convex on a set $S\subset\mathbb{R}^4$, then
--
--   $$
--   \text{the Levi-Civita flow is dynamically convex on } \Sigma_{\mu,c}\cap\Phi^{-1}(S).
--   $$
--
--   That is, every closed Levi-Civita orbit whose image under $\Phi$ lies in $S$ has transverse winding above one, i.e. Conley–Zehnder index at least $3$.
--
--   The Conley–Zehnder index of a periodic orbit is invariant under symplectic changes of coordinates and positive reparametrizations of time. It is computed in any global trivialization of the transverse bundle, and all of these agree because the component is a three-sphere. Statements about indices proved in one regularization, such as those of Liu–Salomão in elliptic-hyperbolic coordinates, therefore transfer to the Levi-Civita model.
--
--   **Formalization Note** The model is `RegularizationModel μ c` from `Def_BirkhoffGlobalSection_RegularizationModel`, and dynamical convexity is `IsDynamicallyConvexOn` from `Def_BirkhoffGlobalSection_DynamicalConvexity`. The hypotheses $0<\mu<1$ and $-c<h_1(\mu)$ make $\Sigma_{\mu,c}$ a compact regular three-sphere.
-- source:
--   Invariance of the Conley--Zehnder index under symplectic conjugacy and positive time reparametrization, as used in Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2, Definition 1.10(i) and Section 10 (indices of the regularized components computed in elliptic-hyperbolic coordinates); Hofer--Wysocki--Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) (index of periodic orbits on three-spheres via a global trivialization).

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

/-- Dynamical convexity does not depend on the regularization. If the model
Hamiltonian flow of a regularization model is dynamically convex on a set `S`,
then the Levi-Civita flow is dynamically convex on the part of the selected
subcritical component that the model maps into `S`. Closed Levi-Civita orbits
are carried to reparametrized closed model orbits, and the transverse winding
is unchanged because the coordinate change is symplectic up to a positive
constant, the time change is positive, and the component is a three-sphere. -/
theorem regularization_model_pulls_back_dynamical_convexity
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : RegularizationModel μ c) (S : Set Phase)
    (hS : IsDynamicallyConvexOn M.modelHamiltonian S) :
    IsDynamicallyConvexOn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c ∩ M.toModel ⁻¹' S) := by sorry

end BirkhoffGlobalSection
