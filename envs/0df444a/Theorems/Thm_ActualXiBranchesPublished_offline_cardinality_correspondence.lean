-- Prove2me | Theorems.Thm_ActualXiBranchesPublished_offline_cardinality_correspondence
-- name    : ActualXiBranchesPublished.offline_cardinality_correspondence
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T09:16:37.28751+00:00
-- url     : https://prove2.me/theorems/f29be298-0eee-4d85-8f1a-1ff985205a79
-- title:
--   Off-line zeros and multiplicity indices have the same finite or infinite classification
-- statement:
--   Let \(I\) be the complete index of upper zeros of the concrete Riemann xi function, with each zero repeated according to its analytic multiplicity. Write \(\rho_i\) for the indexed zero. Let
--   \[E=\{i\in I:\Re\rho_i\ne1/2\},\qquad Z=\{s:\zeta(s)=0,\ 0<\Re s<1,\ \Im s>0,\ \Re s\ne1/2\}.\]
--   Then E is finite if and only if Z is finite; E is nonempty if and only if Z is nonempty; and E is infinite if and only if Z is infinite. This verifies that counting multiplicities does not change the finite/nonempty/infinite classification used in the two branches. It makes no assertion that E or Z is empty, finite, or infinite.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno, PF28 and Branches 2/3 continuation, 2026-11-16. Classical analytic ingredients and conditional integration; no RH proof or novelty claimed. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem ActualXiBranchesPublished.offline_cardinality_correspondence :
    let f : ℂ → ℂ := (fun s : ℂ => (1+s*(s-1)*completedRiemannZeta₀ s)/2)
    let I : Type := (s : {z : ℂ // f z = 0 ∧ 0 < z.im}) × Fin (analyticOrderNatAt f s.val)
    let rho : I → ℂ := fun i => i.1.val
    let offI : Set I := {i | (rho i).re-1/2 ≠ 0}
    let offZ : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧
      0 < s.im ∧ s.re ≠ 1/2}
    (offI.Finite ↔ offZ.Finite) ∧ (offI.Nonempty ↔ offZ.Nonempty) ∧
    (offI.Infinite ↔ offZ.Infinite) := by sorry
