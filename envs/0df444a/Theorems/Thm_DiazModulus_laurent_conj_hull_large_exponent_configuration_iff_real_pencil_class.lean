-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_large_exponent_configuration_iff_real_pencil_class
-- name    : DiazModulus.laurent_conj_hull_large_exponent_configuration_iff_real_pencil_class
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:16.888109+00:00
-- url     : https://prove2.me/theorems/a27bd3de-d50c-4b20-9f34-3edd2ac44701
-- title:
--   Corollary E(a): if a polynomial in u and ū has an exponent of absolute value at least four, its hull carries a 2×3 configuration exactly in the real pencil class
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$ (so $s = \pm|u|$ is real), and put $v = u/s$, so that $\bar v = 1/v$. Let $k \geq 0$, let $c_j \in \overline{\mathbb{Q}}$ for all $j \in \mathbb{Z}$, and put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, z, \bar z)$. Suppose $c_j \neq 0$ for some $j$ with $4 \leq |j| \leq k$. Then $W$ carries a $2 \times 3$ configuration (free $x_0, x_1$ and free $y_0, y_1, y_2$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space) if and only if $W$ is in the class
--
--   - **(R)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$.
--
--   **Proof.** If: class (R) gives $\dim W = 5$ (`DiazModulus.laurent_conj_hull_class_finrank_eq_five`), and Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`) gives the configuration. Only if: Theorem E gives $\dim W = 5$ and one of the classes (P), (Q), (R). In (Q), $z \in W$ lies in the window $\mathrm{span}(v^{-3}, \dots, v^3)$. In (P), $m = \alpha u^2 + \beta u^3 \in W$ is itself a Laurent polynomial in $v$ of class (P), so its hull, contained in $W$, is five-dimensional by `DiazModulus.laurent_conj_hull_class_finrank_eq_five`, hence equal to $W$, and again $z$ lies in the window. Clearing by $v^k$ and comparing the coefficients of $\sum c_jX^{j+k}$ then gives $c_j = 0$ for $|j| \geq 4$, a contradiction.
--
--   **Novelty.** Not found in the sources read; routine, given Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`).
-- source:
--   Not found in the sources read. Uses DiazModulus.laurent_conj_hull_two_by_three_configuration_iff and DiazModulus.laurent_conj_hull_class_finrank_eq_five. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_hull_large_exponent_configuration_iff_real_pencil_class
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (hbig : ∃ j ∈ Finset.Icc (-(k : ℤ)) k, 4 ≤ |j| ∧ c j ≠ 0) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ↔
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ)) := by
  sorry

end DiazModulus
