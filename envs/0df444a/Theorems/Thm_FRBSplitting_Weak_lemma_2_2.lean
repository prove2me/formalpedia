-- Prove2me | Theorems.Thm_FRBSplitting_Weak_lemma_2_2
-- name    : FRBSplitting.Weak.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:59.440172+00:00
-- url     : https://prove2.me/theorems/5bb47e3d-5034-445f-86de-cc5d94ba0e03
-- title:
--   Lemma 2.2, p. 5 — a bounded sequence with lim ‖z_k − z‖ existing at every weak cluster point z converges weakly
-- statement:
--   Let $H$ be a real Hilbert space and $(z_k)\subseteq H$ a bounded sequence. Suppose that for every sequential weak cluster point $z$ of $(z_k)$ the limit
--
--   $$\lim_{k\to\infty}\|z_k-z\|$$
--
--   exists. Then $(z_k)$ is weakly convergent: there is $\bar z\in H$ with $z_k\rightharpoonup\bar z$.
--
--   This Opial-type lemma converts the existence of distance limits into weak convergence; it is the last step of the proof of Theorem 2.5.
--
--   **Formalization Note.** The page says "cluster point"; the proof of Theorem 2.5 applies the lemma to sequential weak cluster points, which is the reading formalized. Weak convergence is $\langle z_k,v\rangle\to\langle\bar z,v\rangle$ for all $v$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 5, Lemma 2.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem lemma_2_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (z : ℕ → H) (hz : Bornology.IsBounded (Set.range z))
    (hlim : ∀ p : H, IsWeakClusterPt z p →
      ∃ l : ℝ, Filter.Tendsto (fun k => ‖z k - p‖) Filter.atTop (nhds l)) :
    ∃ p : H, IsWeakLimit z p := by sorry

end FRBSplitting.Weak
