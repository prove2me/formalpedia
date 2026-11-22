-- Prove2me | Theorems.Thm_Erdos462RH_composite_mass_all_widths
-- name    : Erdos462RH.composite_mass_all_widths
-- status  : Open
-- author  : @adamhenr
-- created : 2026-11-21T09:07:53.750751+00:00
-- url     : https://prove2.me/theorems/603689ee-1e97-4cd9-af46-00e7e3d51bc5
-- title:
--   Composite mass for every fixed positive interval coefficient
-- statement:
--   There is an absolute $K>0$ such that, for every fixed real $C>0$, $\mu_C(x)\le K(1+C)$ for all sufficiently large real $x$ depending on $C$. Under classical RH, for every fixed $C>0$ there are real $c_C>0$ and $X_C$ such that $\mu_C(x)\ge c_C$ for every real $x\ge X_C$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Theorem 1.2, Sections 3–4.

import Definitions.Def_Erdos462Window

namespace Erdos462RH
theorem composite_mass_all_widths :
  (∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, 0 < C → ∃ X : ℝ,
    ∀ x : ℝ, X ≤ x → compositeMass C x ≤ K * (1 + C)) ∧
  (RiemannHypothesis → ∀ C : ℝ, 0 < C → ∃ c X : ℝ, 0 < c ∧
    ∀ x : ℝ, X ≤ x → c ≤ compositeMass C x) := by sorry
end Erdos462RH
