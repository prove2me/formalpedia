-- Prove2me | Theorems.Thm_AgriSubsidy_Combined_prop2_proof_affine
-- name    : AgriSubsidy.Combined.prop2_proof_affine
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:32.803376+00:00
-- url     : https://prove2.me/theorems/6ed9adb0-3593-476e-a818-d3472f2dc0c8
-- title:
--   Proof of Proposition 2, Online Appendix p. 1 — affine invariance of majorization
-- statement:
--   Let $u$ and $v$ be finite real vectors of the same length with $u\ge^m v$. Every common affine transformation, with any real slope $c$ and intercept $d$, preserves their majorization order:
--
--   $$u\ge^m v\quad\Longrightarrow\quad (cu_j+d)_j\ge^m(cv_j+d)_j.$$
--
--   This is the order property cited in the paper's proof of Proposition 2 and used when Cournot output is affine in the farmer ratio.
--
--   **Formalization Note** The slope may be negative or zero, as allowed by the paper's unrestricted planting subsidy.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), Online Appendix p. 1, Proof of Proposition 2; cites Marshall et al. (1979), Theorem A.1.f

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Setting
import Definitions.Def_AgriSubsidy_Combined_Majorization

namespace AgriSubsidy.Combined

theorem prop2_proof_affine {N : ℕ} (u v : Fin N → ℝ)
    (h : Majorizes u v) (c d : ℝ) :
    Majorizes (fun j => c * u j + d) (fun j => c * v j + d) := by sorry

end AgriSubsidy.Combined
