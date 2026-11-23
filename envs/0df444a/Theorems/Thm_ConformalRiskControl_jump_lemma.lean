-- Prove2me | Theorems.Thm_ConformalRiskControl_jump_lemma
-- name    : ConformalRiskControl.jump_lemma
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:12:44.627526+00:00
-- url     : https://prove2.me/theorems/03d1e1da-d492-4d3f-bf58-5c62bd6c7e96
-- title:
--   Lemma 1 (Jump Lemma): jumps of the empirical risk are at most $B/n$
-- statement:
--   Let $a<b$, $\Lambda=[a,b]$, $B\in\mathbb{R}$ and $m\ge1$. Let $L_1,\dots,L_m:\Lambda\to\mathbb{R}$ be i.i.d. random functions. Assume every realisation is non-increasing and right-continuous, $0\le L_i(\lambda)\le B$ for all $\lambda$ almost surely, and for every $i$ and every $\lambda\in(a,b]$,
--   $$\mathbb{P}\big(J(L_i,\lambda)>0\big)=0.$$
--   Then, with $\hat R_m=\frac1m\sum_{i=1}^mL_i$, almost surely
--   $$\sup_{\lambda\in(a,b]}J(\hat R_m,\lambda)\le\frac Bm.$$
--
--   The lemma is the continuity input of the lower bound in Theorem 2. It is applied there to the $n+1$ losses $L_1,\dots,L_{n+1}$.
--
--   **Formalization Note** The paper states the lemma "in the setting of Theorem 2" for $\hat R_n$. The proof uses only the hypotheses listed here, and the proof of Theorem 2 applies the lemma to $n+1$ functions, so it is stated for any number $m$ of i.i.d. functions. The jump is defined through a left limit, so $\Lambda$ is an interval and $\lambda$ ranges over $(a,b]$.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Appendix B, Lemma 1, p. 15 (jump function: Section 2.2, p. 4)

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem jump_lemma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (a b : ℝ) (hab : a < b) (B : ℝ) (L : Fin m → Ω → ℝ → ℝ)
    (hiid : IsIID P (Set.Icc a b) L) (hanti : ∀ i ω, AntitoneOn (L i ω) (Set.Icc a b))
    (hrc : ∀ i ω, IsRightContOn (Set.Icc a b) (L i ω))
    (hbd : ∀ᵐ ω ∂P, ∀ i, ∀ x ∈ Set.Icc a b, 0 ≤ L i ω x ∧ L i ω x ≤ B)
    (hjump : ∀ i, ∀ x ∈ Set.Ioc a b, P {ω | 0 < jump (L i ω) x} = 0) :
    ∀ᵐ ω ∂P, ∀ x ∈ Set.Ioc a b, jump (empRisk fun i => L i ω) x ≤ B / m := by sorry

end ConformalRiskControl
