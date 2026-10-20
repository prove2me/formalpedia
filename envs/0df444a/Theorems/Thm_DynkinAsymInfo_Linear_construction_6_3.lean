-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_construction_6_3
-- name    : DynkinAsymInfo.Linear.construction_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:30.63425+00:00
-- url     : https://prove2.me/theorems/dfe3d4dd-072b-49a4-bfa4-78d7f648519a
-- title:
--   §6.3 (89)–(97) — closed forms solve the boundary systems
-- statement:
--   Assume $\mu_0<0<\mu_1$ and $\varepsilon>0$. The root $\delta$ of (90), the explicit $B$ in (93), and $A=\delta B$ satisfy $0<A<B$. The power-function candidate $V_1$ of (89), extended by (96)–(97), is $C^2$ on $[A,B]$ and satisfies every equation of (81). The candidate scaled value $V$ of (91), extended by (94)–(95), is $C^2$ there and satisfies every equation of (85) and its linear continuation (86).
--
--   These identities establish that the functions in Theorem 6.10 are the boundary-value solutions constructed on the page. The one-sided endpoint derivatives are taken within $[A,B]$.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 23–24, §6.3, (89)–(97)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, pp. 23–24, §6.3,
(89)–(97). The explicit boundaries are positive and ordered. The candidate type-one
and scaled values satisfy their respective boundary-value systems (81), (85), (86).
The derivatives on the closed interval are one-sided at its endpoints. -/
theorem construction_6_3 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) :
    let A := Ab p eps
    let B := Bb p eps
    0 < A ∧ A < B ∧
    ContDiffOn ℝ 2 (V1 p eps) (Set.Icc A B) ∧
    (∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv (V1 p eps)) phi +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * phi * deriv (V1 p eps) phi +
      p.mu1 * V1 p eps phi = 0) ∧
    (∀ phi, 0 < phi → phi ≤ A → V1 p eps phi = 1) ∧
    (∀ phi, B ≤ phi → V1 p eps phi = 1 + eps) ∧
    derivWithin (V1 p eps) (Set.Icc A B) B = 0 ∧
    ContDiffOn ℝ 2 (V p eps) (Set.Icc A B) ∧
    (∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv (V p eps)) phi +
      p.sigma * signalNoise p * phi * deriv (V p eps) phi +
      p.mu0 * V p eps phi = 0) ∧
    (∀ phi, 0 < phi → phi ≤ A → V p eps phi = 1 + phi) ∧
    derivWithin (V p eps) (Set.Icc A B) A = 1 ∧
    derivWithin (V p eps) (Set.Icc A B) B = 1 + eps ∧
    (∀ phi, B ≤ phi → deriv (V p eps) phi = 1 + eps) := by sorry

end DynkinAsymInfo.Linear
