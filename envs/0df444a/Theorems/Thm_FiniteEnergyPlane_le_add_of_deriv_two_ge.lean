-- Prove2me | Theorems.Thm_FiniteEnergyPlane_le_add_of_deriv_two_ge
-- name    : FiniteEnergyPlane.le_add_of_deriv_two_ge
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T22:40:17.923997+00:00
-- url     : https://prove2.me/theorems/d63bf4ba-92d2-47f3-b3a4-4fe172d1cd8f
-- title:
--   Pointwise bound from a lower bound on the second derivative and a bounded primitive
-- statement:
--   Let $s,B,B',L\in\mathbb{R}$ with $B\ge0$, and let $H,H_1,H_2,D,D_1:\mathbb{R}\to\mathbb{R}$. Suppose that for every $x\in[s-1,s+1]$: $H'(x)=H_1(x)$, $H_1'(x)=H_2(x)$, $H_2(x)\ge-B$, $D'(x)=D_1(x)$, $D_1(x)\ge H(x)-B'$ and $|D(x)|\le L$. Then
--   $$H(s)\le L+\tfrac{B}{2}+B'.$$
--
--   This one-variable estimate turns information on a window into a pointwise bound at its centre.
--
--   **Formalization Note** All derivatives are `HasDerivAt` statements at each point of `Icc (s - 1) (s + 1)`.
-- source:
--   Standard; used for C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Lemma 4.8.8

import Mathlib

namespace FiniteEnergyPlane

open Set

/-- On `[s - 1, s + 1]`, let `H' = H₁`, `H₁' = H₂ ≥ -B` with `B ≥ 0`, and let `D' = D₁` with
`D₁ ≥ H - B'` and `|D| ≤ L`. Then `H(s) ≤ L + B / 2 + B'`. -/
theorem le_add_of_deriv_two_ge (H H1 H2 D Dd : ℝ → ℝ) (s B B' L : ℝ) (hB : 0 ≤ B)
    (hH : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt H (H1 x) x)
    (hH1 : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt H1 (H2 x) x)
    (hH2 : ∀ x ∈ Icc (s - 1) (s + 1), -B ≤ H2 x)
    (hDd : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt D (Dd x) x)
    (hDH : ∀ x ∈ Icc (s - 1) (s + 1), H x - B' ≤ Dd x)
    (hL : ∀ x ∈ Icc (s - 1) (s + 1), |D x| ≤ L) :
    H s ≤ L + B / 2 + B' := by
  sorry

end FiniteEnergyPlane
