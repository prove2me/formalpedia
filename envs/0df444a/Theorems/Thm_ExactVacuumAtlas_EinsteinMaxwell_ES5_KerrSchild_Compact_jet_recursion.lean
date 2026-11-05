-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Compact_jet_recursion
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact.jet_recursion
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:21.107503+00:00
-- url     : https://prove2.me/theorems/9388eef9-792b-4316-ba66-d7e24ebe3deb
-- title:
--   Triangular recursion
-- statement:
--   **Triangular recursion.** Pivots `4, 3, 6, 3, 8, 18, 12, 15` only; `B₃` cancels in
--   `2 PM₃ - 3 PC₃`. No division by `M, h, J, Q, c`; all degenerate parameter values included.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/JetRecursion.lean#L242-L272; SHA-256 964aa1eef07e6bbdfccea1fb3f3a0b336471f529f25beee82e3e987bc2ab0274. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedResiduals
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteJetObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_JetRecursion
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
open Polynomial
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
variable {M h J Q c : ℝ} {F b A : ℝ[X]}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact.jet_recursion (hn : JetNormalization M c F b A) (hr : SelectedRows h Q J F b A) :
    b.coeff 1 = jetB1 M h J Q c ∧ F.coeff 2 = jetF2 M h J Q c ∧ b.coeff 2 = jetB2 M h J Q c ∧
    A.coeff 2 = jetA2 M h J Q c ∧ A.coeff 3 = jetA3 M h J Q c ∧ F.coeff 3 = jetF3 M h J Q c ∧
    b.coeff 3 = jetB3 M h J Q c ∧ A.coeff 4 = jetA4 M h J Q c := by sorry
