-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Compact_vii04_compactified_jet_recursion
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact.vii04_compactified_jet_recursion
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:20.7328+00:00
-- url     : https://prove2.me/theorems/29ce0fcf-a06c-41b1-8b62-c464f87ccd9e
-- title:
--   VII-04 root (F2c1), "equation-sourced finite-coefficient obstruction"
-- statement:
--   **VII-04 root (F2c1), "equation-sourced finite-coefficient obstruction".** For arbitrary
--   `F b A : Polynomial ℝ` with only the leading normalisation and the eight selected coefficient
--   equations of the actual compactified residual polynomials: the recursion outputs
--   `B₁ F₂ B₂ A₂ A₃ F₃ B₃ A₄`; the generic Γ coefficients 6–8 coincide with F1's; and their vanishing
--   forces `J³Q⁵ = 0`, i.e. `J = 0 ∨ Q = 0`. Not an asymptotic or KS statement about real solutions
--   (F2c2, F3 pending).
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/JetRecursion.lean#L317-L337; SHA-256 964aa1eef07e6bbdfccea1fb3f3a0b336471f529f25beee82e3e987bc2ab0274. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact.vii04_compactified_jet_recursion (M h J Q c : ℝ) (F b A : ℝ[X])
    (hn : JetNormalization M c F b A) (hr : SelectedRows h Q J F b A) :
    (b.coeff 1 = jetB1 M h J Q c ∧ F.coeff 2 = jetF2 M h J Q c ∧ b.coeff 2 = jetB2 M h J Q c ∧
      A.coeff 2 = jetA2 M h J Q c ∧ A.coeff 3 = jetA3 M h J Q c ∧ F.coeff 3 = jetF3 M h J Q c ∧
      b.coeff 3 = jetB3 M h J Q c ∧ A.coeff 4 = jetA4 M h J Q c) ∧
    ((gammaGen h Q J F b A).coeff 6 = (FiniteJet.gammaJet M h J Q c).coeff 6 ∧
      (gammaGen h Q J F b A).coeff 7 = (FiniteJet.gammaJet M h J Q c).coeff 7 ∧
      (gammaGen h Q J F b A).coeff 8 = (FiniteJet.gammaJet M h J Q c).coeff 8) ∧
    ((gammaGen h Q J F b A).coeff 6 = 0 → (gammaGen h Q J F b A).coeff 7 = 0 →
      (gammaGen h Q J F b A).coeff 8 = 0 → J ^ 3 * Q ^ 5 = 0 ∧ (J = 0 ∨ Q = 0)) := by sorry
