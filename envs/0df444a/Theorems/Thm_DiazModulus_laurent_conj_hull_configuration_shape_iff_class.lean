-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_configuration_shape_iff_class
-- name    : DiazModulus.laurent_conj_hull_configuration_shape_iff_class
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T11:54:51.127831+00:00
-- url     : https://prove2.me/theorems/0e35095f-1635-43b5-b8be-fb64c275ee02
-- title:
--   For a Laurent polynomial z in u/s with a five-dimensional conjugation hull, Theorem F's shapes D1, D2a, D2b hold exactly when Theorem E's classes (P), (Q), (R) do
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$, and put $v = u/s$. Let $k \geq 0$, let $c_j \in \overline{\mathbb{Q}}$ for $j \in \mathbb{Z}$, put $z = \sum_{j=-k}^{k} c_jv^j$, and let $W = \mathrm{span}(1, u, \bar u, z, \bar z)$, the conjugation hull of $z$. Suppose $\dim W = 5$. Then $W$ has one of Theorem F's shapes (D1), (D2a), (D2b) if and only if it is in one of Theorem E's classes (P), (Q), (R).
--
--   Theorem F's shapes:
--
--   - **(D1)** there are linearly independent $t_0, t_1, t_2 \in \mathbb{C}$ with $t_j \in W$ and $ut_j \in W$ for every $j$;
--   - **(D2a, two-orbit)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), P'(u)S_2(u)/(uQ'(u)))$ for some $P', Q', S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P', Q'$ coprime, $\max(\deg P', \deg Q') = 2$ and $\deg S_1, \deg S_2 \leq 2$;
--   - **(D2b, cyclic)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), Q'(u)(Q'(u)S_1(u) + P'(u)S_2(u))/(uP'(u)^2))$ for some such $P', Q', S_1, S_2$.
--
--   Theorem E's classes:
--
--   - **(P)** $\alpha u^2 + \beta u^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero;
--   - **(Q)** $W = \mathrm{span}(1, u, \bar u, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$;
--   - **(R)** $W = \mathrm{span}(1, u, \bar u, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$.
--
--   Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`) and Theorem F (`DiazModulus.rational_conj_hull_two_by_three_configuration_iff`) both say when $W$ carries a $2 \times 3$ configuration; this node says that, for Laurent $z$, their criteria agree.
--
--   **Proof.** Put $\rho = u\bar u = s^2$, which is algebraic as $s$ is. Since $s \in \overline{\mathbb{Q}}$, $v = u/s$ lies in the field $\overline{\mathbb{Q}}(u)$, and so do its integer powers and $z$. Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`, 10.98) says that $W$ carries a $2 \times 3$ configuration if and only if $\dim W = 5$ and $W$ is of class (P), (Q) or (R). Theorem F (`DiazModulus.rational_conj_hull_two_by_three_configuration_iff`, 10.146), which applies because $\rho$ is algebraic and $z \in \overline{\mathbb{Q}}(u)$, says that $W$ carries one if and only if either $\dim W = 4$ and $z \in \mathrm{span}(1, u, \bar u, (u - a)^{-1})$ for some $a \in \overline{\mathbb{Q}}$ with $a\bar a = \rho$, or $\dim W = 5$ and $W$ has shape (D1), (D2a) or (D2b). As $\dim W = 5$, the dimension-four alternative is excluded. So (D1), (D2a) or (D2b) gives a configuration by Theorem F, hence (P), (Q) or (R) by Theorem E; and (P), (Q) or (R) gives a configuration by Theorem E, hence (D1), (D2a) or (D2b) by Theorem F. The proof uses Theorem E: it does not derive Theorem E from Theorem F.
--
--   **Novelty.** Not found in the sources read; routine. A corollary of two equivalences: Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`, 10.98) and Theorem F (`DiazModulus.rational_conj_hull_two_by_three_configuration_iff`, 10.146) both say when the hull carries a $2 \times 3$ configuration, and Theorem F asks Theorem E's question for every $z$ rational in $u$. That their criteria agree on Laurent hulls was earlier checked by exact computation only; here it is proved. The proof goes through Theorem E: it does not derive Theorem E from Theorem F, and Theorem E's explicit criteria still do not follow from Theorem F. The explicit maps from the classes to the shapes are `DiazModulus.laurent_polynomial_class_conj_hull_two_orbit_form` ((P) to (D2a)), `DiazModulus.laurent_involution_class_space_cyclic_form` ((Q) to (D2b)) and `DiazModulus.laurent_real_pencil_class_space_u_multiplier_triple` ((R) to (D1)).
-- source:
--   Not found in the sources read. A corollary of Theorem E (DiazModulus.laurent_conj_hull_two_by_three_configuration_iff, 10.98) and Theorem F (DiazModulus.rational_conj_hull_two_by_three_configuration_iff, 10.146), which both say when the conjugation hull carries a 2 × 3 configuration; Theorem F asks Theorem E's question for every z rational in u. The proof uses Theorem E, so it does not derive Theorem E from Theorem F, and Theorem E's explicit criteria still do not follow from Theorem F. The explicit maps from E's classes to F's shapes are DiazModulus.laurent_polynomial_class_conj_hull_two_orbit_form, DiazModulus.laurent_involution_class_space_cyclic_form and DiazModulus.laurent_real_pencil_class_space_u_multiplier_triple. Uses DiazModulus.laurent_conj_hull_two_by_three_configuration_iff and DiazModulus.rational_conj_hull_two_by_three_configuration_iff. R21a of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_conj_hull_configuration_shape_iff_class
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) = 5) :
    ((∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) ∧ u * t j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
      (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ))) ↔
    ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G)), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) := by
  sorry

end DiazModulus
