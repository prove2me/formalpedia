-- Prove2me | Theorems.Thm_DiazModulus_laurent_polynomial_class_conj_hull_two_orbit_form
-- name    : DiazModulus.laurent_polynomial_class_conj_hull_two_orbit_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T11:55:03.404327+00:00
-- url     : https://prove2.me/theorems/aa05d508-a30f-4f4c-9fe6-893fbb763388
-- title:
--   If a non-zero α u² + β u³ (α, β algebraic) lies in the conjugation hull of z = Σ c_j (u/s)^j, the hull is Theorem F's two-orbit space D2a for the pencil (X², 1)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$, and put $v = u/s$. Let $k \geq 0$, let $c_j \in \mathbb{C}$ for $j \in \mathbb{Z}$ be arbitrary, put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}(1, u, \bar u, z, \bar z)$. Let $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero, with $\alpha u^2 + \beta u^3 \in W$ (Theorem E's class (P)). Then there are $P', Q', S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P'(u) = u^2$, $Q'(u) = 1$, $S_1(u) = \bar\beta s^6 + \bar\alpha s^4u$ and $S_2(u) = \alpha u + \beta u^2$, such that $P', Q'$ are coprime, $\max(\deg P', \deg Q') = 2$, $\deg S_1, \deg S_2 \leq 2$, and $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), P'(u)S_2(u)/(uQ'(u)))$.
--
--   That is, $W$ has Theorem F's shape (D2a) with $P' = X^2$ and $Q' = 1$ ($u$ being transcendental, the values at $u$ determine the polynomials), and $W = \mathrm{span}(1, u, u^{-1}, \bar w, w)$ for $w = \alpha u^2 + \beta u^3$. No dimension hypothesis is made, and the $c_j$ are not assumed algebraic, as the proof does not need it.
--
--   **Proof.** As $u \neq 0$ and $s^2 = u\bar u$, $s \neq 0$ and $\bar u = s^2/u$. Write $w = \alpha u^2 + \beta u^3$; then $\bar w = (\bar\beta s^6 + \bar\alpha s^4u)/u^3$. Take $P' = X^2$ and $Q' = 1$ (coprime, of maximal degree $2$), $S_1 = \bar\beta s^6 + \bar\alpha s^4X$ and $S_2 = \alpha X + \beta X^2$, with coefficients in $\overline{\mathbb{Q}}$ because complex conjugation maps $\overline{\mathbb{Q}}$ to itself; then $Q'(u)S_1(u)/(uP'(u)) = \bar w$ and $P'(u)S_2(u)/(uQ'(u)) = w$. (1) The five vectors $1, u, u^{-1}, \bar w, w$ lie in $W$: $u^{-1} = s^{-2}\bar u$; $w \in W$ by hypothesis; and $W$ is stable under complex conjugation, since conjugation permutes its generators $1, u, \bar u, z, \bar z$ and maps $\overline{\mathbb{Q}}$ to itself, so $\bar w \in W$. (2) They are linearly independent: multiplying a relation $x_0 + x_1u + x_2u^{-1} + x_3\bar w + x_4w = 0$ by $u^3$ gives a polynomial in $u$ of degree at most $6$ with coefficients $x_3\bar\beta s^6, x_3\bar\alpha s^4, x_2, x_0, x_1, x_4\alpha, x_4\beta$, all algebraic; as $u$ is transcendental they vanish, and $(\alpha, \beta) \neq (0, 0)$, $s \neq 0$ give $x_3 = x_4 = 0$. (3) $W$ is spanned by five vectors, so $\dim W \leq 5$, and the inclusion of the five-dimensional span of (1) in $W$ is an equality. Nothing about $z$ is used beyond the hull, so the $c_j$ need not be algebraic.
--
--   **Novelty.** Not found in the sources read; routine. It writes Theorem E's class (P) in the coordinates of Theorem F: every hull of class (P) has shape (D2a), with the pencil $(X^2, 1)$. The configuration of class (P) is in print: Diaz (2007, Théorème 7(1)), already in Diaz (2004, Théorème 2).
-- source:
--   Not found in the sources read. Theorem E's class (P) (DiazModulus.laurent_conj_hull_two_by_three_configuration_iff) in the coordinates of Theorem F (DiazModulus.rational_conj_hull_two_by_three_configuration_iff). The configuration of class (P) is in print: G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 7(1), and already G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorème 2. R21a of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_polynomial_class_conj_hull_two_orbit_form
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ)
    (α β : ℂ) (hα : α ∈ Qbar) (hβ : β ∈ Qbar) (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hP : α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) :
    ∃ P' Q' S₁ S₂ : (↥Qbar)[X], aeval u P' = u ^ 2 ∧ aeval u Q' = 1 ∧
      aeval u S₁ = conj β * s ^ 6 + conj α * s ^ 4 * u ∧ aeval u S₂ = α * u + β * u ^ 2 ∧
      IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧ S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
      Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ) := by
  sorry

end DiazModulus
