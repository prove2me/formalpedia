-- Prove2me | Theorems.Thm_ActualXiBranchesPublished_concrete_xi_branches_from_five_inputs
-- name    : ActualXiBranchesPublished.concrete_xi_branches_from_five_inputs
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T09:16:44.187996+00:00
-- url     : https://prove2.me/theorems/b9623e48-e4ba-4d0c-ad37-2e3ed6c4b3ac
-- title:
--   Concrete xi-derived Q: finite and infinite branch contradictions under five explicit inputs
-- statement:
--   Let I index the upper zeros of the concrete Riemann xi function with their exact analytic multiplicities. Put \(\rho_i=1/2+\epsilon_i+i\gamma_i\), \(B_i=-(\rho_i-1/2)^2\), \(G(x)=\Re\xi(1/2+\sqrt{x})\), \(J(x)=\log G(x)-\log G(0)\), and
--   \[Q_n(u)=2^n u^{2n-1}(-1)^{n-1}J^{(n)}(u^2).\]
--   Assume five inputs: every \(\gamma_i\ge2\); \(\gamma_i\le1000\) implies \(\epsilon_i=0\); at least one \(\gamma_i\le100\); for every \(y\ge1\), every finite set of indices with \(\gamma_i^2\le y\) has size at most \(y^{3/4}\); and
--   \[G(x)/G(0)=\prod_{i\in I}(1+x/B_i)\quad(x>0).\]
--   Then \(Q_n(u)>0\), hence \(Q_n(u)\ge0\), for every \(n\ge1\) and \(u>0\). Let N be the assertion that some such Q is negative, and let Z be the set of all nontrivial zeta zeros off the critical line (both half-planes). The finite branch concludes \(\neg(N\land Z\text{ finite and nonempty})\); the infinite branch concludes \(\neg(N\land Z\text{ infinite})\).
--   The functions and zero index are concrete, and positivity of G and its normalizing constant are deduced, not assumed. The five inputs remain explicit proof obligations. These branch statements do not exclude off-line zeros in isolation and do not prove RH.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno, PF28 and Branches 2/3 continuation, 2026-11-16. Classical analytic ingredients and conditional integration; no RH proof or novelty claimed. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem ActualXiBranchesPublished.concrete_xi_branches_from_five_inputs :
    let f : ℂ → ℂ := (fun s : ℂ => (1+s*(s-1)*completedRiemannZeta₀ s)/2)
    let I : Type := (s : {z : ℂ // f z = 0 ∧ 0 < z.im}) × Fin (analyticOrderNatAt f s.val)
    let rho : I → ℂ := fun i => i.1.val
    let gamma : I → ℝ := fun i => (rho i).im
    let eps : I → ℝ := fun i => (rho i).re-1/2
    let g : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (g x) - Real.log (g 0)) (u^2)
    let off : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2}
    (∀ i, 2 ≤ gamma i) →
    (∀ i, gamma i ≤ 1000 → eps i = 0) →
    (∃ i, gamma i ≤ 100) →
    (∀ y ≥ (1 : ℝ), ∀ F : Finset I,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ y^((3 : ℝ)/4)) →
    (∀ x > 0, ((g x / g 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/(-(rho i-1/2)^2))) →
    (¬ ((∃ n ≥ 1, ∃ u > 0, q n u < 0) ∧ off.Finite ∧ off.Nonempty)) ∧
    (¬ ((∃ n ≥ 1, ∃ u > 0, q n u < 0) ∧ off.Infinite)) ∧
    (∀ n ≥ 1, ∀ u > 0, 0 ≤ q n u) ∧
    (∀ n ≥ 1, ∀ u > 0, 0 < q n u) := by sorry
