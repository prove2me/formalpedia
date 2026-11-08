-- Prove2me | Theorems.Thm_DegreeSensitivity_exists_beats_kushilevitz
-- name    : DegreeSensitivity.exists_beats_kushilevitz
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:52:43.438947+00:00
-- url     : https://prove2.me/theorems/290cec13-4fa3-46bf-97a5-0bb135eb728a
-- title:
--   A Boolean function beating the Kushilevitz exponent
-- statement:
--   There exist $n > 1$ and a Boolean function $f$ on $n$ bits with $\deg(f) > 1$ whose sensitivity at the origin exceeds $\deg(f)^{\log 6/\log 3}$. Equivalently, $s(f,\mathbf 0) = \deg(f)^{\alpha}$ for some $\alpha > \log 6/\log 3$.
-- source:
--   Epoch AI, FrontierMath Open Problems, "Degree vs. Sensitivity for Boolean Functions", https://epoch.ai/files/open-problems/degree-sensitivity-boolean.pdf, Problem statement, equation (1). The web submission format additionally caps n <= 100; this statement does not.

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DegreeSensitivity

theorem exists_beats_kushilevitz :
    ∃ (n : ℕ) (f : BoolFunc n), 1 < n ∧ 1 < polyDegree f ∧
      (polyDegree f : ℝ) ^ (Real.log 6 / Real.log 3) <
        (sensitivityAt f (fun _ => false) : ℝ) := by sorry

end DegreeSensitivity
