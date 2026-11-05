-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Radial_quadratic_of_deriv_deriv_eq_two
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial.quadratic_of_deriv_deriv_eq_two
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:03:25.792562+00:00
-- url     : https://prove2.me/theorems/3ab3ed2f-2064-453e-88d2-3d118c2b38f0
-- title:
--   On a preconnected open I, a C^∞ function with genuine N'' = 2 on I is
--   R² + βR + γ on I, with β = N'(r₀) - 2r₀, γ = N(r₀) - r₀² - βr₀
-- statement:
--   On a preconnected open `I`, a `C^∞` function with genuine `N'' = 2` on `I` is
--   `R² + βR + γ` on `I`, with `β = N'(r₀) - 2r₀`, `γ = N(r₀) - r₀² - βr₀`.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/RadialBVPEquivalence.lean#L125-L151; SHA-256 1c5fd5df80379b7e3ee16c565f6b9e90260a032061230e358e16e3dcc8b569a9. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
open scoped ContDiff Topology
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ} {r : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial.quadratic_of_deriv_deriv_eq_two {N : ℝ → ℝ} (hIo : IsOpen I) (hI : IsPreconnected I)
    (hN : ContDiffOn ℝ ∞ N I) {r₀ : ℝ} (hr₀ : r₀ ∈ I)
    (h2 : ∀ r ∈ I, deriv (deriv N) r = 2) :
    ∃ β γ : ℝ, β = deriv N r₀ - 2 * r₀ ∧ γ = N r₀ - r₀ ^ 2 - β * r₀ ∧
      ∀ r ∈ I, N r = r ^ 2 + β * r + γ := by sorry
