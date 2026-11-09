-- Prove2me | Theorems.Thm_CondGeoVerif_program_lipschitz
-- name    : CondGeoVerif.program_lipschitz
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:28:27.779855+00:00
-- url     : https://prove2.me/theorems/eb778d3a-3f6c-4549-8217-726d464efcd9
-- title:
--   $|M_{j,\eta}(D)-M_{j,\eta}(D')|\le\mathbb E|D-D'|$
-- statement:
--   Let $0<\eta<1/2$, $j\in\{0,1\}$, and let $D,D':\mathbb R^r\to\{0,1\}$ be Borel. For either program,
--   $$|M_{j,\eta}(D)-M_{j,\eta}(D')|\le\mathbb E|D(G)-D'(G)|,\qquad G\sim N(0,I_r).$$
--   This makes the envelopes continuous in the contraction and the competitor.
--
--   Differences from the source:
--   - encoding: E|D − D′| → the Gaussian measure of {D ≠ D′}; reason: equal for {0,1}-valued indicators
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §A.3, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_CondGeoVerif_Mprog

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **The programs are 1-Lipschitz in the disagreement set** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, §A.3, p.16 = PDF p.19):
"For either program, `|M_{j,η}(D) − M_{j,η}(D′)| ≤ E|D − D′|`", for Borel `D, D' : ℝʳ → {0, 1}`
and `G ∼ N(0, I_r)`.

**Formalization Note** For `{0, 1}`-valued `D, D'`, `E|D − D'|` is the Gaussian measure of
`{D ≠ D'}`. The noise bound is the standing `0 < η < 1/2`. -/
theorem program_lipschitz {r : ℕ} {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) (j : Fin 2)
    (D D' : Vec r → Bool) (hD : Measurable D) (hD' : Measurable D') :
    |Mprog j η D - Mprog j η D'| ≤ (gauss r {z | D z ≠ D' z}).toReal := by sorry

end CondGeoVerif
