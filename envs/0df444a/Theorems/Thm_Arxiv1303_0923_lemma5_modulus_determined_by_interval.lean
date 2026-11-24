-- Prove2me | Theorems.Thm_Arxiv1303_0923_lemma5_modulus_determined_by_interval
-- name    : Arxiv1303_0923.lemma5_modulus_determined_by_interval
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:29:08.702477+00:00
-- url     : https://prove2.me/theorems/e714be7d-2aa4-43ef-aebc-f7d178f6a4fb
-- title:
--   Lemma 5: the modulus of a real-analytic function is determined on $\mathbb{R}$ by its values on $(a,b)$
-- statement:
--   Let $a<b$ and let $d_1,d_2:\mathbb{R}\to\mathbb{C}$ be real-analytic at every point of $\mathbb{R}$. If $|d_1(k)|=|d_2(k)|$ for all $k\in(a,b)$, then
--   $$|d_1(k)|=|d_2(k)|\quad\text{for all }k\in\mathbb{R}.$$
--
--   In words: the modulus of a function analytic on the real line is uniquely determined on all of $\mathbb{R}$ by its values on an arbitrary interval. It extends the phaseless data from $(a,b)$ to the whole real line.
--
--   **Formalization Note** The paper's sentence omits a verb ("can be uniquely for all $k$"); "uniquely determined" is the evident reading and is stated as the comparison of two such functions.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c009; Section 3.2, Lemma 5, PDF p. 9 (argument in Section 1.1, p. 3)

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem lemma5_modulus_determined_by_interval (a b : ℝ) (hab : a < b) (d1 d2 : ℝ → ℂ)
    (hd1 : ∀ k : ℝ, AnalyticAt ℝ d1 k) (hd2 : ∀ k : ℝ, AnalyticAt ℝ d2 k)
    (h : ∀ k ∈ Set.Ioo a b, ‖d1 k‖ = ‖d2 k‖) :
    ∀ k : ℝ, ‖d1 k‖ = ‖d2 k‖ := by sorry

end Arxiv1303_0923
