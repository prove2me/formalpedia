-- Prove2me | Theorems.Thm_DiazModulus_cubic_window_hull_real_pencil_class_iff
-- name    : DiazModulus.cubic_window_hull_real_pencil_class_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:08.947655+00:00
-- url     : https://prove2.me/theorems/df8da70c-b1f3-4b7b-9e70-c021470f3a4f
-- title:
--   For z ≡ a v̄³ + b v̄² + c v² + d v³ mod span(1, v, v̄), the hull is in the real pencil class exactly when |a c̄ − b d̄| = ||a|² − |d|²| ≠ 0
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $a, b, c, d \in \overline{\mathbb{Q}}$ and let $z \in \mathbb{C}$ with $z - (a\bar v^3 + b\bar v^2 + cv^2 + dv^3) \in \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v)$, and let $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, z, \bar z)$ (no assumption is made on $\dim W$). Then $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$, if and only if
--
--   $$|a\bar c - b\bar d|^2 = (a\bar a - d\bar d)^2 \quad\text{and}\quad a\bar a - d\bar d \neq 0.$$
--
--   **Proof.** Here $W = \mathrm{span}(1, v, \bar v, m, \bar m)$ with $m = a\bar v^3 + b\bar v^2 + cv^2 + dv^3$; write $p_{12} = a\bar c - b\bar d$ and $p_{14} = a\bar a - d\bar d$ (the dimension of $W$ is not needed: $p_{14} \neq 0$ already makes $m, \bar m$ free modulo $\mathrm{span}(1, v, \bar v)$). If $g = x_0 + x_1v + x_2\bar v + xm + y\bar m$ and $f_{-3}, f_{-2}, f_2, f_3$ are the coefficients of $xm + y\bar m$, then $G(v) - (x_0 + x_1v + f_2v^2 + f_3v^3) = \bar v\,\overline{Q(v)}$ for $Q = \bar x_2 + \bar f_{-2}X + \bar f_{-3}X^2 - \bar\kappa G$; multiplied by $v^{n+1}$, $n = \deg Q$, the left side has order at least $n + 1$ and the right side degree at most $n$, so both vanish, as $v$ is transcendental. Hence $G = x_0 + x_1X + f_2X^2 + f_3X^3$ and $\bar\kappa G = \bar x_2 + \bar f_{-2}X + \bar f_{-3}X^2$, so $f_3 = 0$, $f_{-3} = \kappa\bar f_2$ and $f_2 \neq 0$ as $\deg G \geq 2$; with $D = x\bar x - y\bar y$ the Plücker identities give $Dp_{14} = f_2\bar f_2 \neq 0$ and $Dp_{12} = \kappa\bar f_2^2$, so $p_{14} \neq 0$ and $p_{12}\bar p_{12} = p_{14}^2$. Conversely $\kappa = p_{14}/p_{12}$ has $\kappa\bar\kappa = 1$; with $G = G_1X + \bar p_{12}X^2$, $G_1 = \kappa\,\overline{\bar ab - d\bar c}$, one has $g = G_1v + (\bar am - d\bar m)$ and $\bar g = \bar G_1\bar v + (a\bar m - \bar dm)$, and the determinant $a\bar a - d\bar d = p_{14} \neq 0$ of this change of basis gives $W = \mathrm{span}(1, v, \bar v, g, \bar g)$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cubic_window_hull_real_pencil_class_iff
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (z a b c d : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (hd : d ∈ Qbar)
    (hz : z - (a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3) ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ)) :
    (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ)) ↔
      ((a * conj c - b * conj d) * conj (a * conj c - b * conj d) = (a * conj a - d * conj d) ^ 2 ∧ (a * conj a - d * conj d) ≠ 0) := by
  sorry

end DiazModulus
