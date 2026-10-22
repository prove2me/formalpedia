-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_validated_binding_global_sections_of_convexity
-- name    : BirkhoffGlobalSection.validated_binding_global_sections_of_convexity
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-29T17:39:33.910984+00:00
-- url     : https://prove2.me/theorems/a594273e-0242-48bd-a13f-60340387de48
-- title:
--   Validated binding global sections from convexity
-- statement:
--   Let $0<\mu\leq 1/2$ and $2.1\leq c\leq 2.1+10^{-6}$. Assume the radial filling of the selected Levi-Civita energy component is convex. Then the validated retrograde and direct periodic orbits exist with the strict astronomical sign conditions, and each orbit bounds an ordinary disk-like global surface of section.
--
--   This isolates the dynamical and contact-topological part of Joung--van Koert Theorems 1.2 and 1.5 from the analytic convexity proof. Theorem 1.2 supplies symmetric unknotted binding orbits of self-linking number $-1$; convexity gives dynamical convexity, and Hryniewicz's criterion then gives the two disk-like global sections.
--
--   **Formalization Note** The convexity hypothesis is stated using the radial filling already used by the platform theorem `BirkhoffGlobalSection.convex_left_energy_component`. The mass-zero endpoint is omitted to match the parent milestone.
-- source:
--   Joung--van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Theorems 1.2, 1.3, and 1.5; Proposition 2.2; proof of Theorem 3.1. Positive-mass restriction matching the parent milestone.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

/-- Joung--van Koert, Theorems 1.2 and 1.5, with the convexity conclusion
isolated as a hypothesis: the validated retrograde and direct binding orbits
each bound a disk-like global surface of section. -/
theorem validated_binding_global_sections_of_convexity (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hconvex :
      Convex ℝ {y : Phase | ∃ s ∈ leftEnergyComponent μ c,
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}) :
    ∃ γr γd : PeriodicOrbit φ,
      IsAstronomicallyRetrogradeOrbit φ γr ∧
      IsAstronomicallyDirectOrbit φ γd ∧
      DiskLikeGlobalSurfaceOfSection φ γr ∧
      DiskLikeGlobalSurfaceOfSection φ γd := by sorry

end BirkhoffGlobalSection
