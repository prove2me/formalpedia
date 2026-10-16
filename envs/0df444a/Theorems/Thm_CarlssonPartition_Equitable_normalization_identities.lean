-- Prove2me | Theorems.Thm_CarlssonPartition_Equitable_normalization_identities
-- name    : CarlssonPartition.Equitable.normalization_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:12.054429+00:00
-- url     : https://prove2.me/theorems/18eb53b9-2f93-4c01-ae35-18c6c8b528f5
-- title:
--   Proof of Theorem 6, p. ec6 — ∬_{R_i}√f_i = ∬_{R_i}√f/√(∬_{R_i}f) and ∬_{R_i}‖x − x₀‖f_i = ∬_{R_i}‖x − x₀‖f/∬_{R_i}f
-- statement:
--   Let $(\mathscr R,x_0,f,m,v,q,\bar s,\beta)$ satisfy the standing assumptions, and let $S\subseteq\mathscr R$ be a measurable subregion with conditional density $f_S(x)=f(x)/\iint_S f(y)\,dy$. Then
--   $$\iint_S\sqrt{f_S(x)}\,dx=\frac{\iint_S\sqrt{f(x)}\,dx}{\sqrt{\iint_S f(x)\,dx}},\qquad \iint_S\|x-x_0\|\,f_S(x)\,dx=\frac{\iint_S\|x-x_0\|\,f(x)\,dx}{\iint_S f(x)\,dx}.$$
--
--   These two identities convert Theorem 3 applied inside one district, which is written in the district's conditional density, back into integrals of the original density $f$; they are the third equality of the chain in the proof of Theorem 6.
--
--   **Formalization Note.** No positivity of $\iint_S f$ is assumed: it is nonnegative because $f\ge0$ on $\mathscr R$, and when it is $0$ both sides of each identity are $0$ under Lean's convention $a/0=0$.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. ec6, proof of Theorem 6, paragraph after the first display

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

open Filter Topology MeasureTheory

namespace CarlssonPartition.Equitable

theorem normalization_identities (I : Instance) (hI : I.Standing)
    (S : Set Plane) (hS : NullMeasurableSet S volume) (hSR : S ⊆ I.R) :
    (∫ x in S, Real.sqrt (I.fSub S x)) = (∫ x in S, Real.sqrt (I.f x)) / Real.sqrt (I.pr S) ∧
    (∫ x in S, ‖x - I.x0‖ * I.fSub S x) = (∫ x in S, ‖x - I.x0‖ * I.f x) / I.pr S := by sorry

end CarlssonPartition.Equitable
