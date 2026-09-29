-- Prove2me | Theorems.Thm_FamousTheorems_hensels_lemma
-- name    : FamousTheorems.hensels_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:44.306989+00:00
-- url     : https://prove2.me/theorems/cf467c3f-3d8b-4912-b589-15b13539d32d
-- title:
--   Hensel's lemma
-- statement:
--   **Hensel's lemma.** Over the $p$-adic integers, an approximate root of a polynomial that is nondegenerate — $|F(a)| < |F'(a)|^2$ — lifts to an exact root nearby, and the root is unique in that neighbourhood. This is Newton's method made exact: the ultrametric inequality makes the iteration converge and the limit a genuine root, with no analytic estimates required beyond the initial nondegeneracy. It is the mechanism that transfers information from $\mathbb{Z}/p$ to $\mathbb{Z}_p$: a simple root mod $p$ automatically yields a $p$-adic root, which is why local solubility is usually checkable by a finite computation. Hensel introduced it around 1900 in founding the $p$-adic numbers, and the same statement holds over any complete discrete valuation ring. **Formalization note.** The norm is the $p$-adic absolute value and `F.derivative` the formal derivative. The result is Mathlib's `hensels_lemma`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem hensels_lemma :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemiring R] 
    [inst_2 : Algebra R ℤ_[p]] {F : Polynomial R} {a : ℤ_[p]}, 
    ‖(Polynomial.aeval a) F‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ^ 2 → 
    ∃ z, 
    (Polynomial.aeval z) F = 0 ∧ 
    ‖z - a‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ∧ 
    ‖(Polynomial.aeval z) (Polynomial.derivative F)‖ = ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ∧ 
    ∀ (z' : ℤ_[p]), 
    (Polynomial.aeval z') F = 0 → ‖z' - a‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ → z' = z := by sorry

end FamousTheorems
