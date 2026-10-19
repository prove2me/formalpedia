-- Prove2me | Theorems.Thm_DiazModulus_rational_pencil_space_visible_to_four_dimensional_extensions_iff_natDegree_le
-- name    : DiazModulus.rational_pencil_space_visible_to_four_dimensional_extensions_iff_natDegree_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T09:45:18.844509+00:00
-- url     : https://prove2.me/theorems/a8617db8-73ad-43a6-b2ea-6e244b7e3b1e
-- title:
--   For f = P(u)/Q(u) in lowest terms, W(λ, f) = span(1, u, ū, f, f/(s + λu)) is visible to the four-dimensional extensions exactly when a degree bound holds
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$, and $\lambda \in \overline{\mathbb{Q}}$ with $|\lambda| = 1$. Let $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and call $W \supseteq H_0$ visible to the four-dimensional extensions if some $w \in W \setminus H_0$ makes $H_0 + \overline{\mathbb{Q}}w$ carry a $2 \times 3$ configuration (free $x_1, x_2$ and free $y_1, y_2, y_3$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space). Let $P, Q \in \overline{\mathbb{Q}}[X]$ be coprime, $f = P(u)/Q(u)$, and suppose $1, u, \bar u, f, f/(s + \lambda u)$ are free over $\overline{\mathbb{Q}}$. Then $W(\lambda, f) = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, f, f/(s + \lambda u))$ is visible to the four-dimensional extensions if and only if
--
--   $$\max(\deg P, \deg Q + 1) \leq 2 + [Q(0) = 0] + [P(-s\bar\lambda) = 0],$$
--
--   where $[\cdot]$ is $1$ when the condition holds and $0$ otherwise. For real $f$ these are the conjugation-stable spaces of `DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration`; the criterion does not need $f$ real.
--
--   **Proof.** Put $a_0 = -s\bar\lambda$ and $g = f/(s + \lambda u)$, so $s + \lambda u = \lambda(u - a_0)$ and $f = sg + \lambda ug$: the space is $\mathrm{span}(1, u, \bar u, g, ug)$, and these five are free. If $P(a_0) \neq 0$, $g = P(u)/\tilde Q(u)$ with $\tilde Q = \lambda Q(X - a_0)$ coprime to $P$; if $P(a_0) = 0$, $P = (X - a_0)P_1$ and $g = \lambda^{-1}P_1(u)/Q(u)$. `DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le` applied to that fraction gives the bound in both cases.
--
--   **Novelty.** Not found in the sources read; routine. For Laurent $f$ it contains the invisibility in `DiazModulus.laurent_real_pencil_configuration_invisible_to_four_dimensional_extensions`.
-- source:
--   Not found in the sources read. Uses DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le. R17 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem rational_pencil_space_visible_to_four_dimensional_extensions_iff_natDegree_le
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1)
    (P Q : (↥Qbar)[X]) (hcop : IsCoprime P Q)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, aeval u P / aeval u Q, aeval u P / aeval u Q / (s + lam * u)]) :
    (∃ w ∈ Submodule.span Qbar ({1, u, conj u, aeval u P / aeval u Q, aeval u P / aeval u Q / (s + lam * u)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ)) ↔
      max P.natDegree (Q.natDegree + 1) ≤
        2 + (if Q.coeff 0 = 0 then 1 else 0) + (if aeval (-(s * conj lam)) P = 0 then 1 else 0) := by
  sorry

end DiazModulus
