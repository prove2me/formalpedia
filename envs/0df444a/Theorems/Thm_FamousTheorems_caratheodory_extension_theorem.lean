-- Prove2me | Theorems.Thm_FamousTheorems_caratheodory_extension_theorem
-- name    : FamousTheorems.caratheodory_extension_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:12.223318+00:00
-- url     : https://prove2.me/theorems/0302adbc-1aba-4c3b-a217-b499d8d4836f
-- title:
--   Carathéodory's extension theorem
-- statement:
--   **Carathéodory's extension theorem.** Let $\mathcal C$ be a semiring of subsets of $\alpha$ that generates the $\sigma$-algebra of $\alpha$, and let $m$ be a finitely additive, countably subadditive content on $\mathcal C$ with values in $[0,\infty]$. Then there is a measure $\mu$ on $\alpha$ that extends $m$: $\mu(s)=m(s)$ for all $s\in\mathcal C$.
--
--   This is how measures are built in practice. Lebesgue measure extends length on intervals, product measures extend the product of measures on rectangles, and the Kolmogorov extension theorem extends consistent finite-dimensional distributions.
--
--   **Formalization note.** Mathlib's `MeasureTheory.AddContent.measure_eq`, with witness `m.measure`. `IsSetSemiring C` is the semiring condition (closed under finite intersection, and differences are finite disjoint unions), `AddContent ENNReal C` is a finitely additive content, and `m.IsSigmaSubadditive` is countable subadditivity on $\mathcal C$. The measurable-space structure is assumed to equal `MeasurableSpace.generateFrom C`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.AddContent.measure_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem caratheodory_extension_theorem {α : Type*} [mα : MeasurableSpace α] {C : Set (Set α)} (m : AddContent ENNReal C)
    (hC : IsSetSemiring C) (hC_gen : mα = MeasurableSpace.generateFrom C) (hm : m.IsSigmaSubadditive) :
    ∃ μ : Measure α, ∀ s ∈ C, μ s = m s := by sorry

end FamousTheorems
