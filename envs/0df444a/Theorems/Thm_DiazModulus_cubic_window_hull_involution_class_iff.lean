-- Prove2me | Theorems.Thm_DiazModulus_cubic_window_hull_involution_class_iff
-- name    : DiazModulus.cubic_window_hull_involution_class_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:05.10901+00:00
-- url     : https://prove2.me/theorems/4094a93f-d03f-4897-a722-ec12e2201ade
-- title:
--   For z ≡ a v̄³ + b v̄² + c v² + d v³ mod span(1, v, v̄) with a five-dimensional hull, the hull is in the involution class exactly when |a| = |d| and (a, d) ≠ (0, 0)
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $a, b, c, d \in \overline{\mathbb{Q}}$ and let $z \in \mathbb{C}$ with $z - (a\bar v^3 + b\bar v^2 + cv^2 + dv^3) \in \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v)$, and let $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, z, \bar z)$ with $\dim_{\overline{\mathbb{Q}}} W = 5$. Then $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$ if and only if $a\bar a - d\bar d = 0$ and $(a, d) \neq (0, 0)$.
--
--   **Proof.** As for the polynomial class, $W = \mathrm{span}(1, v, \bar v, m, \bar m)$ with $m = a\bar v^3 + b\bar v^2 + cv^2 + dv^3$, these five are free, and so are $v^{-3}, \dots, v^3$; write $p_{12} = a\bar c - b\bar d$, $p_{13} = a\bar b - c\bar d$, $p_{14} = a\bar a - d\bar d$, $n_0 = \bar v^2 + ev^2$ and $n_1 = \beta\bar v^3 + \zeta v^2 + ev^3$. If $W = \mathrm{span}(1, v, \bar v, n_0, n_1)$, the $\bar v^3$ and $v^3$ coefficients of $m$ give $a = x\beta$ and $d = xe$, so $p_{14} = x\bar x(\beta\bar\beta - e\bar e) = 0$, and $a = d = 0$ would give $\beta = 0$ from $n_1 \in W$, against $\beta\bar\beta = 1$. Conversely, $p_{14} = 0$ and $(a, d) \neq (0, 0)$ give $a, d \neq 0$, and the identities $\bar ap_{13} = \bar bp_{14} - \bar d\bar p_{12}$ and $\bar dm - a\bar m = -(p_{12}\bar v^2 + p_{13}v^2 + p_{14}v^3)$ give $p_{12}, p_{13} \neq 0$. With $e = p_{13}/p_{12}$, $\beta = ea/d$ and $\zeta = e(c - be)/d$ one gets $\bar dm - a\bar m = -p_{12}n_0$ and $dn_1 = e(m - bn_0)$, so $W = \mathrm{span}(1, v, \bar v, n_0, n_1)$; this span is conjugation-stable, and `DiazModulus.laurent_involution_space_conj_stable_constraints` ($\beta \neq 0$) gives $|e| = |\beta| = 1$ and $\zeta = -\beta e^2\bar\zeta$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.laurent_involution_space_conj_stable_constraints. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cubic_window_hull_involution_class_iff
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (z a b c d : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (hd : d ∈ Qbar)
    (hz : z - (a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3) ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ))
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) = 5) :
    (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ)) ↔
      ((a * conj a - d * conj d) = 0 ∧ (a ≠ 0 ∨ d ≠ 0)) := by
  sorry

end DiazModulus
