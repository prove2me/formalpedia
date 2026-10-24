-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_faraday_frame
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.faraday_frame
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:19.935263+00:00
-- url     : https://prove2.me/theorems/031862f9-6a49-4cd2-b324-07e6bb0b7750
-- title:
--   KN Faraday frame matrix
-- statement:
--   KN Faraday frame matrix
--
--   All 16 bilinear frame components F(e_A, e_B) of faradayKN on domReg.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN Faraday 场 16 个标架分量。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNFaraday.lean#L141-L152; SHA-256 cab1226e82c48431de6bcae27caa3784dedabf5a67e7c2bb040fee2dce482b03. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_Kerr_InAtoms
open Real
open scoped ComplexConjugate Matrix
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del faradayKN domReg)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {M a Q : ℝ} {x : Pt 4}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.faraday_frame (hx : x ∈ domReg M a Q) (A B : Fin 4) :
    ccontr (faradayKN a Q) x (knFrame M a Q x A) (knFrame M a Q x B) =
      (!![0, ((Q * (x 1 ^ 2 - a ^ 2 * cos (x 2) ^ 2) / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ), 0, 0;
          -((Q * (x 1 ^ 2 - a ^ 2 * cos (x 2) ^ 2) / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ), 0, 0, 0;
          0, 0, 0, -(2 * Complex.I * ((Q * a * x 1 * cos (x 2) / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ));
          0, 0, 2 * Complex.I * ((Q * a * x 1 * cos (x 2) / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ), 0] :
        Matrix (Fin 4) (Fin 4) ℂ) A B := by sorry
