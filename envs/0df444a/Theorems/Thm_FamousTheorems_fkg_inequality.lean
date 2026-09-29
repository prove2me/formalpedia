-- Prove2me | Theorems.Thm_FamousTheorems_fkg_inequality
-- name    : FamousTheorems.fkg_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:37.646829+00:00
-- url     : https://prove2.me/theorems/b1a82c4d-2359-491f-9cb7-eb8eb1d51ad6
-- title:
--   The FKG inequality
-- statement:
--   **The FKG inequality.** Let $\alpha$ be a finite distributive lattice and $\mu:\alpha\to\mathbb R_{\ge0}$ log-supermodular, i.e. $\mu(a)\mu(b)\le\mu(a\wedge b)\mu(a\vee b)$ for all $a,b$. If $f,g:\alpha\to\mathbb R_{\ge0}$ are monotone, then
--   $$\Big(\sum_a\mu(a)f(a)\Big)\Big(\sum_a\mu(a)g(a)\Big)\le\Big(\sum_a\mu(a)\Big)\Big(\sum_a\mu(a)f(a)g(a)\Big).$$
--
--   In probabilistic language, increasing functions are positively correlated under such a measure. The Fortuin–Kasteleyn–Ginibre inequality is a basic tool in percolation, statistical mechanics and random graphs. It contains Harris's inequality as a special case.
--
--   **Formalization note.** Mathlib's `fkg`, stated there for a general linearly ordered commutative semiring; here the values are taken in $\mathbb R$. The hypotheses `0 ≤ μ`, `0 ≤ f`, `0 ≤ g` are pointwise nonnegativity.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `fkg`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fkg_inequality {α : Type*} [DistribLattice α] [Fintype α] (f g μ : α → ℝ) (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a, μ a * g a ≤ (∑ a, μ a) * ∑ a, μ a * (f a * g a) := by sorry

end FamousTheorems
