-- Prove2me | Theorems.Thm_DiazModulus_cubic_window_conj_hull_two_by_three_configuration_iff_criterion
-- name    : DiazModulus.cubic_window_conj_hull_two_by_three_configuration_iff_criterion
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:03.819539+00:00
-- url     : https://prove2.me/theorems/36cec08d-92d4-4e5a-9498-174b72caf5f2
-- title:
--   Corollary E(b): for z ≡ Aū³ + Bū² + Cu² + Du³ with a five-dimensional hull, a 2×3 configuration exists iff NΔ(|Δ|² − |u|²N²) = 0, N = |A|² − |D|², Δ = AC̄ − BD̄
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$ (so $s = \pm|u|$ is real), and put $v = u/s$, so that $\bar v = 1/v$. Let $A, B, C, D \in \overline{\mathbb{Q}}$, let $z \in \mathbb{C}$ with $z - (A\bar u^3 + B\bar u^2 + Cu^2 + Du^3) \in \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u)$, and let $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, z, \bar z)$ with $\dim_{\overline{\mathbb{Q}}} W = 5$. Put $\Delta = A\bar C - B\bar D$ and $N = A\bar A - D\bar D$, and consider the classes
--
--   - **(P)** $\alpha u^2 + \beta u^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero;
--   - **(Q)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$;
--   - **(R)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$.
--
--   Then:
--
--   - $W$ is in class (P) if and only if $\Delta = 0$;
--   - $W$ is in class (Q) if and only if $N = 0$ and $(A, D) \neq (0, 0)$;
--   - $W$ is in class (R) if and only if $|\Delta|^2 = s^2N^2$ and $N \neq 0$;
--   - $W$ carries a $2 \times 3$ configuration (free $x_0, x_1$ and free $y_0, y_1, y_2$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space) if and only if $N\Delta\,(|\Delta|^2 - s^2N^2) = 0$.
--
--   Here $s^2 = |u|^2$.
--
--   **Proof.** $s$ is real since $s^2 = |u|^2 > 0$, so $v = u/s$ has $v\bar v = 1$ and $v \notin \overline{\mathbb{Q}}$, $\mathrm{span}(1, u, \bar u, \cdot, \cdot) = \mathrm{span}(1, v, \bar v, \cdot, \cdot)$, and $z \equiv a\bar v^3 + b\bar v^2 + cv^2 + dv^3$ with $a = As^3$, $b = Bs^2$, $c = Cs^2$, $d = Ds^3$, so that $a\bar c - b\bar d = s^5\Delta$ and $a\bar a - d\bar d = s^6N$. The three classes are then read off `DiazModulus.cubic_window_hull_polynomial_class_iff`, `DiazModulus.cubic_window_hull_involution_class_iff` and `DiazModulus.cubic_window_hull_real_pencil_class_iff` (for (P), $\alpha u^2 + \beta u^3 = (\alpha s^2)v^2 + (\beta s^3)v^3$). Writing $z = \sum_{|j| \leq 3} c_jv^j$, Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`, $k = 3$) says that $W$ carries a configuration exactly when it is in one of the classes, that is $\Delta = 0$, or $N = 0$ with $(A, D) \neq (0, 0)$, or $|\Delta|^2 = s^2N^2$ with $N \neq 0$; since $A = D = 0$ forces $\Delta = 0$, this is $N\Delta(|\Delta|^2 - s^2N^2) = 0$.
--
--   **Novelty.** Not found in the sources read; routine, given Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`).
-- source:
--   Not found in the sources read. Uses DiazModulus.laurent_conj_hull_two_by_three_configuration_iff, DiazModulus.cubic_window_hull_polynomial_class_iff, DiazModulus.cubic_window_hull_involution_class_iff and DiazModulus.cubic_window_hull_real_pencil_class_iff. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cubic_window_conj_hull_two_by_three_configuration_iff_criterion
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (z A B C D : ℂ) (hA : A ∈ Qbar) (hB : B ∈ Qbar) (hC : C ∈ Qbar) (hD : D ∈ Qbar)
    (hz : z - (A * conj u ^ 3 + B * conj u ^ 2 + C * u ^ 2 + D * u ^ 3) ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ))
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 5) :
    ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ↔ (A * conj C - B * conj D) = 0) ∧
    ((∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ↔
      ((A * conj A - D * conj D) = 0 ∧ (A ≠ 0 ∨ D ≠ 0))) ∧
    ((∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ)) ↔
      ((A * conj C - B * conj D) * conj (A * conj C - B * conj D) = s ^ 2 * (A * conj A - D * conj D) ^ 2 ∧ (A * conj A - D * conj D) ≠ 0)) ∧
    ((∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ↔
      (A * conj A - D * conj D) * (A * conj C - B * conj D) * ((A * conj C - B * conj D) * conj (A * conj C - B * conj D) - s ^ 2 * (A * conj A - D * conj D) ^ 2) = 0) := by
  sorry

end DiazModulus
