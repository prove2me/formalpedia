-- Prove2me | Theorems.Thm_DiffVI_Exist_lemma_6_3
-- name    : DiffVI.Exist.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:16.00998+00:00
-- url     : https://prove2.me/theorems/71b334b6-ebda-48c0-b564-0a6b83c7efbe
-- title:
--   Lemma 6.3 (Filippov's implicit function theorem), pp. 30–31 — measurable selection u with u(t) ∈ U(t, x(t)), v(t) = h(t, x(t), u(t)) a.e.
-- statement:
--   Let $T>0$ and $\Omega=[0,T]\times\mathbb R^n$. Let $h:\Omega\times\mathbb R^m\to\mathbb R^n$ be continuous and let $U:\Omega\rightrightarrows\mathbb R^m$ be a closed set-valued map (its graph is closed) such that, for some $\eta_U>0$,
--   $$\sup_{u\in U(t,x)}\|u\|\le\eta_U(1+\|x\|)\qquad\forall (t,x)\in\Omega.$$
--   Let $v:[0,T]\to\mathbb R^n$ be measurable and $x:[0,T]\to\mathbb R^n$ continuous, with $v(t)\in h(t,x(t),U(t,x(t)))$ for almost every $t\in[0,T]$. Then there is a measurable $u:[0,T]\to\mathbb R^m$ with
--   $$u(t)\in U(t,x(t))\quad\text{and}\quad v(t)=h(t,x(t),u(t))\qquad\text{for almost every }t\in[0,T].$$
--
--   This measurable-selection lemma converts a solution of the differential inclusion with right-hand side (6.4) into a solution pair of the DVI.
--
--   **Formalization Note** "Measurable" for $v$ is almost-everywhere measurability for Lebesgue measure on $[0,T]$; the selection $u$ is produced Borel measurable on $\mathbb R$. Continuity of $h$ is continuity on $\Omega\times\mathbb R^m$. The paper cites this result without proof.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 30–31, Lemma 6.3 (Filippov [42])

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Lemma 6.3 (Filippov's implicit function theorem [42]), pp. 30–31: measurable selection for
`v(t) ∈ h(t, x(t), U(t, x(t)))` with `h` continuous on `Ω × ℝᵐ` and `U` a closed set-valued map
on `Ω` with linear growth. -/
theorem lemma_6_3 {n m : ℕ} (T : ℝ) (hT : 0 < T)
    (h : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (hh : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
      h p.1 p.2.1 p.2.2) (Set.Icc 0 T ×ˢ Set.univ))
    (U : ℝ → EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin m)))
    (hUcl : IsClosed {p : ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) |
      p.1 ∈ Set.Icc 0 T ∧ p.2.2 ∈ U p.1 p.2.1})
    (hUgrowth : ∃ ηU : ℝ, 0 < ηU ∧
      ∀ t ∈ Set.Icc 0 T, ∀ x, ∀ u ∈ U t x, ‖u‖ ≤ ηU * (1 + ‖x‖))
    (v : ℝ → EuclideanSpace ℝ (Fin n)) (hv : AEMeasurable v (volume.restrict (Set.Icc 0 T)))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : ContinuousOn x (Set.Icc 0 T))
    (hvx : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      v t ∈ (fun u => h t (x t) u) '' U t (x t)) :
    ∃ u : ℝ → EuclideanSpace ℝ (Fin m), Measurable u ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), u t ∈ U t (x t) ∧ v t = h t (x t) (u t) := by sorry

end DiffVI.Exist
