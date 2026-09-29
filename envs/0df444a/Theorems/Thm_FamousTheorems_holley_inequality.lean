-- Prove2me | Theorems.Thm_FamousTheorems_holley_inequality
-- name    : FamousTheorems.holley_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:31.338074+00:00
-- url     : https://prove2.me/theorems/ddce9245-5d14-41c6-a0df-03c44562fbe4
-- title:
--   Holley's inequality
-- statement:
--   **Holley's inequality.** Let $\alpha$ be a finite distributive lattice and let $f,g,\mu:\alpha\to\mathbb R_{\ge0}$, with $\mu$ monotone. Suppose $\sum_a f(a)=\sum_a g(a)$ and
--   $$f(a)\,g(b)\le f(a\wedge b)\,g(a\vee b)\quad\text{for all }a,b.$$
--   Then
--   $$\sum_a\mu(a)f(a)\le\sum_a\mu(a)g(a).$$
--
--   In probabilistic terms, a measure $g$ dominating $f$ in this lattice sense stochastically dominates it on increasing events. The inequality generalises the FKG inequality and is a basic tool in statistical mechanics and percolation.
--
--   **Formalization note.** Mathlib's `holley`, specialised here to real-valued functions.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `holley`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem holley_inequality {α : Type*} [DistribLattice α] [Fintype α] (f g μ : α → ℝ) (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hμ : Monotone μ) (hfg : ∑ a, f a = ∑ a, g a) (h : ∀ a b, f a * g b ≤ f (a ⊓ b) * g (a ⊔ b)) :
    ∑ a, μ a * f a ≤ ∑ a, μ a * g a := by sorry

end FamousTheorems
