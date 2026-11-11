-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_2_7
-- name    : CosetTreeSVP.SVP.lemma_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:32:35.351321+00:00
-- url     : https://prove2.me/theorems/ecc44189-40ac-40e1-8132-4d0c0a3c186d
-- title:
--   Lemma 2.7 — if ‖x − y‖ ≤ ε‖y‖ with 0 ≤ ε < 1 and y ≠ 0, then x ≠ 0 and ‖x/‖x‖ − y/‖y‖‖ ≤ 2ε/(1 − ε)
-- statement:
--   **Lemma 2.7.** Let $x, y \in \mathbb R^n$ with $y \ne 0$ and $0 \le \varepsilon < 1$. If $\|x - y\| \le \varepsilon\|y\|$, then $x \ne 0$ and
--   $$\left\|\frac{x}{\|x\|} - \frac{y}{\|y\|}\right\| \le \frac{2\varepsilon}{1-\varepsilon}.$$
--   It turns an approximation of $v$ up to a scalar into an approximation of its direction (used in Lemma 4.2).
--
--   Differences from the source: none.
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 12 (PDF 14), Lemma 2.7

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_2_7 {n : ℕ} (x y : E n) (hy : y ≠ 0) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hxy : ‖x - y‖ ≤ ε * ‖y‖) :
    x ≠ 0 ∧ ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ε / (1 - ε) := by sorry

end CosetTreeSVP.SVP
