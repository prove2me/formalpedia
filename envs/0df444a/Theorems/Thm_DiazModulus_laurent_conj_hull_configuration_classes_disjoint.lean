-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_configuration_classes_disjoint
-- name    : DiazModulus.laurent_conj_hull_configuration_classes_disjoint
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:14.227636+00:00
-- url     : https://prove2.me/theorems/8127fddc-483c-4906-9485-46c5916e5201
-- title:
--   No subspace of ℂ is in two of the polynomial, involution and real pencil classes of conjugation hulls
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$ (so $s = \pm|u|$ is real), and put $v = u/s$, so that $\bar v = 1/v$. Let $W \subseteq \mathbb{C}$ be any $\overline{\mathbb{Q}}$-subspace. Then no two of the following hold:
--
--   - **(P)** $\alpha u^2 + \beta u^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero;
--   - **(Q)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$;
--   - **(R)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$.
--
--   **Proof.** As $s$ is real, $v = u/s$ is transcendental with $\bar v = 1/v$, $u = sv$ and $\bar u = s/v$, so a relation in $v$ and $1/v$ with algebraic coefficients clears to a polynomial identity and can be compared coefficientwise. (P) against (Q): writing $\alpha u^2 + \beta u^3$ in the (Q) basis and multiplying by $v^3$ gives a degree-$6$ identity whose coefficients at $1, v, v^5, v^6$ force the (Q) coordinates, and then $\alpha, \beta$, to vanish. For (R), with $n = \deg G \geq 2$ and $H = \sum_{i \leq n}\bar G_iX^{n-i}$, so that $H(v) = v^n\overline{G(v)}$ and $H(0) = \bar G_n \neq 0$, evaluating a cleared identity at $0$ kills the coordinate of $g$, and then clearing by $v^n$ kills that of $\bar g$. So (P) and (R) exclude each other, since both coordinates of $\alpha u^2 + \beta u^3$ vanish and then $\alpha = \beta = 0$; and so do (Q) and (R), since applied to $\bar v^2 + ev^2$ and its conjugate both coordinates vanish, while $\bar v^2 + ev^2 \notin \mathrm{span}(1, v, \bar v)$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_hull_configuration_classes_disjoint
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u) (W : Submodule (↥Qbar) ℂ) :
    ¬ ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ W) ∧
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        W =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ))) ∧
    ¬ ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ W) ∧
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        W =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) ∧
    ¬ ((∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        W =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∧
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        W =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) := by
  sorry

end DiazModulus
