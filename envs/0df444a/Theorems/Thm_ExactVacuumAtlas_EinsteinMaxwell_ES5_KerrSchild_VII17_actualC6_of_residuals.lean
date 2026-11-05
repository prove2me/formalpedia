-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VII17_actualC6_of_residuals
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII17.actualC6_of_residuals
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:05:25.964755+00:00
-- url     : https://prove2.me/theorems/e4c425e5-a2e3-486e-bf07-c59f3bd13c39
-- title:
--   Finite $C^6$ regularity of the actual asymptotic branch from the Einstein–Maxwell residuals
-- statement:
--   Finite $C^6$ regularity of the actual asymptotic branch from the Einstein–Maxwell residuals
--
--   For the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta, let $(f, m, N, w, p, a)$ be actual radial data on an open set $I$ satisfying the paper boundary-value system with integration constants $Q, J$, with $N(R) = (R-s)(R-s-h)$ real-factored ($s, h \in \mathbb{R}$) and the tail $(s+\varepsilon^{-1}, \infty) \subset I$. With $x = (R-s)^{-1}$, $F(x) = f(s + x^{-1})$, $b(x) = x\, m(s + x^{-1})$, $A(x) = a(s + x^{-1})$, assume the value asymptotics $|F - (1 + f_1 x)| \le C_F x^2$, $|b - (1 + b_1 x)| \le C_b x^2$, $|A - a_1 x| \le C_A x^2$ on $(0, \varepsilon)$ (values only, no derivative asymptotics). Then for some $0 < \eta \le \varepsilon$ there are independent real functions $F_e, b_e, A_e$, of class $C^6$ on $(-\eta, \eta)$, agreeing with $F, b, A$ on $(0, \eta)$, with $F_e(0) = b_e(0) = 1$, $A_e(0) = 0$ (the Lean predicate `FiniteBranch6`). The $C^6$ extension is a consequence of the actual field equations, not an input.
--
--   **Scope.** Five-dimensional, $\Lambda = 0$, source-free pure Einstein–Maxwell; equal-magnitude two-angular-momentum radial ansatz; real-factored $N$ and the actual first-order value-asymptotic branch (the paper's Eq. 33 branch; it is not derived here from weaker asymptotic-flatness bounds). $Q$, $J$ are the actual radial conservation constants; their normalisation to total charge and angular momentum follows the source and is not formalised as flux integrals. The Kerr–Schild conclusion concerns representations covering a complete tail of the original chart; it is not a statement that charged rotating black holes do not exist and certifies no horizon or solution. **Attribution.** The physical obstruction appears in Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60); the project contributes the finite-regularity applicability proof on actual solutions and its formal certification; no priority is claimed.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/VII17C6Bridge.lean#L446-L514; SHA-256 4db645ee1ed6a785adc2eecde4f7cdbe7ab576f706b3c7cd3dc8d264520bebdb. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedBridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedResiduals
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteJetObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylorJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_JetRecursion
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_OneSidedExtraction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII13FiniteBranchSpec
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII16AsymptoticBridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII17Algebra
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII17Analysis
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII17C6Bridge
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII17
open Filter Set Topology ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII13FiniteBranchSpec

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII17.actualC6_of_residuals
    {s h Q J ε : ℝ} (hε : 0 < ε)
    {I : Set ℝ} {f m N w p a : ℝ → ℝ}
    (hP : PaperData I f m N w p a)
    (hN : FactorizedN I N s h)
    (hB : PaperBVP I f m N w p a Q J)
    (htail : Set.Ioi (s + ε⁻¹) ⊆ I)
    {f₁ b₁ a₁ C_F C_b C_A : ℝ}
    (hCF : 0 ≤ C_F) (hCb : 0 ≤ C_b) (hCA : 0 ≤ C_A)
    (hvalF : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pull  s f x - (1 + f₁ * x)| ≤ C_F * x ^ 2)
    (hvalb : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pullM s m x - (1 + b₁ * x)| ≤ C_b * x ^ 2)
    (hvalA : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pull  s a x - a₁ * x|       ≤ C_A * x ^ 2) :
    ∃ η, 0 < η ∧ η ≤ ε ∧ ∃ Fe be Ae : ℝ → ℝ, FiniteBranch6 I s η f m a Fe be Ae := by sorry
