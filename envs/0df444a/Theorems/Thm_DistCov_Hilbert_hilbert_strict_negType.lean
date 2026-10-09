-- Prove2me | Theorems.Thm_DistCov_Hilbert_hilbert_strict_negType
-- name    : DistCov.Hilbert.hilbert_strict_negType
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:31.633384+00:00
-- url     : https://prove2.me/theorems/98164fd0-c3b0-4d16-8e93-964298127a04
-- title:
--   p. 18 — every (real) Hilbert space has negative type, indeed strict negative type
-- statement:
--   Let $H$ be a real Hilbert space with distance $d(x,y)=\|x-y\|$. Then:
--
--   1. $H$ has negative type: for all $n$, all $x_1,\dots,x_n\in H$ and all real $\alpha_1,\dots,\alpha_n$ with $\sum_i\alpha_i=0$,
--   $$\sum_{i,j\le n}\alpha_i\alpha_j\,\|x_i-x_j\|\le 0 ;$$
--   2. $H$ has strict negative type: if moreover the points $x_1,\dots,x_n$ are distinct and the double sum equals $0$, then $\alpha_1=\dots=\alpha_n=0$.
--
--   Clause 2 is the restriction of strong negative type to measures of finite support (p. 11): for finitely supported $\mu_1,\mu_2$, $D(\mu_1-\mu_2)=0$ forces $\mu_1=\mu_2$. The paper derives the statement from the Euclidean case; it supplies the negative-type half of Theorem 3.16.
--
--   **Formalization Note.** Hilbert spaces are real (Errata (viii)); a complex Hilbert space has the same distances as its realification. Strict negative type is stated directly on weights $\alpha$ at distinct points, which is the finite-support case of the condition on p. 11.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 18, paragraph before Theorem 3.16; strict negative type defined on p. 11; Errata (viii), p. 27

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem hilbert_strict_negType (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    DistCov.Indep.NegType H ∧
    ∀ (n : ℕ) (x : Fin n → H) (α : Fin n → ℝ), Function.Injective x → ∑ i, α i = 0 →
      ∑ i, ∑ j, α i * α j * dist (x i) (x j) = 0 → α = 0 := by sorry

end DistCov.Hilbert
