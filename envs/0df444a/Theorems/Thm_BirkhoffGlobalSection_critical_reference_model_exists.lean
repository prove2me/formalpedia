-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_critical_reference_model_exists
-- name    : BirkhoffGlobalSection.critical_reference_model_exists
-- status  : Disproved
-- author  : @Sneed
-- created : 2026-09-30T05:57:37.11298+00:00
-- url     : https://prove2.me/theorems/e67eabc8-aa39-4d76-9382-731756f2d2c1
-- title:
--   Critical EH reference model lands in the estimate region
-- statement:
--   Existence of the elliptic-hyperbolic reference model at the critical parameters.
--
--   Let $U$ be an open neighborhood in model phase space of the two saddle-center points $(\\pm 1/2,0,0,0)$. At mass ratio $\\mu=1/2$ there exists a regularization model $M_0$ whose model Hamiltonian equals the explicit elliptic-hyperbolic critical Hamiltonian $\\hat{H}$ of Section 9.2, and whose image of the left energy component of the critical surface, outside $U$, lies in the first-quadrant estimate region where Theorem 9.4 applies:
--
--   $$M_0.\\mathrm{modelHamiltonian}=\\hat{H},\\qquad M_0(s)\\in \\mathcal{H}_1\\ \text{for all } s\\in \\Sigma_{\\mathrm{left}}\\setminus U.
--   $$
--
--   This is the Section 9.2 construction step of the critical convexity theorem: it fixes one faithful reference Hamiltonian and reduces the global claim to estimates on that reference.
--
--   **Formalization Note** Phase points use model coordinates $![y_1,y_2,x_1,x_2]$; $\\hat{H}$ and the estimate region are `ehCriticalHamiltonian` and `ehEstimateRegion` from `BirkhoffGlobalSection_EHCriticalConvexity`.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2, Section 9.2 (elliptic-hyperbolic regularization, mu = 1/2, h = -2), Section 9.3 (Theorems 9.1 and 9.4, eq. 9.11), and Theorem 1.12 as used in Section 10.

import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Definitions.Def_BirkhoffGlobalSection_EHCriticalConvexity

namespace BirkhoffGlobalSection

theorem critical_reference_model_exists
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ M₀ : RegularizationModel (1 / 2) 2,
      M₀.modelHamiltonian = ehCriticalHamiltonian ∧
      ∀ s ∈ leftEnergyComponent (1 / 2) 2, s ∉ U → M₀.toModel s ∈ ehEstimateRegion := by sorry

end BirkhoffGlobalSection
