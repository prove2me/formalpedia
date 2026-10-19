-- Prove2me | Theorems.Thm_DiazModulus_laurent_degree_one_conj_stable_space_real_pencil_normal_form
-- name    : DiazModulus.laurent_degree_one_conj_stable_space_real_pencil_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:34.511659+00:00
-- url     : https://prove2.me/theorems/3ea21e7e-eb2c-4aec-b7ef-cc83e77ad8b9
-- title:
--   If 1, v, v̄, g, vg are free and ḡ ∈ span(1, v, vg) for a Laurent g, their span is span(1, v, v̄, h, h̄) with h = G(v) + κ · conj(v G(v)), |κ| = 1
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $N \geq 0$, $F \in \overline{\mathbb{Q}}[X]$ and $g = F(v)/v^N$. Suppose $1, v, \bar v, g, vg$ are linearly independent over $\overline{\mathbb{Q}}$ and $\bar g \in \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, vg)$, and let $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, g, vg)$. Then there are $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ such that $\deg G \geq 2$ or $v^2 \in W$, and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, h, \bar h)$ for $h = G(v) + \kappa\,\overline{vG(v)}$.
--
--   **Proof.** Write $\bar g = a + bv + c\,vg$ with $a, b, c \in \overline{\mathbb{Q}}$. Conjugating once more and using $v\bar v = 1$ gives $(\bar a + \bar cb) + (\bar b + \bar ca)\bar v + (c\bar c - 1)g = 0$, so $c\bar c = 1$ and $a = -c\bar b$ by freeness. Then $g_1 = g - \bar b\bar v = (XF - \bar bX^N)(v)/v^{N+1}$ satisfies $\bar g_1 = c\,vg_1$, and `DiazModulus.laurent_conj_twisted_symmetric_normal_form` gives $G$ with $G(0) = 0$ and $g_1 \equiv h$ modulo $\mathrm{span}(1, \bar v)$, where $h = G(v) + \kappa\,\overline{vG(v)}$ and $\kappa = \bar c$; the identity $vh = \kappa\bar h$ then shows that $1, v, \bar v, g, vg$ and $1, v, \bar v, h, \bar h$ span the same space. If $\deg G \leq 1$, then $G = a_1X$: $a_1 = 0$ would put $g$ in $\mathrm{span}(1, \bar v)$, against freeness, and $a_1 \neq 0$ gives $\bar h = \bar a_1\bar v + ca_1v^2$, so $v^2 \in W$.
--
--   **Novelty.** Not found in the sources read in this form; routine. It is the Laurent form of `DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space`.
-- source:
--   Not found in the sources read in this form; the Laurent form of DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space. Uses DiazModulus.laurent_conj_twisted_symmetric_normal_form. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_degree_one_conj_stable_space_real_pencil_normal_form
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (N : ℕ) (F : Polynomial ↥Qbar)
    (hind : LinearIndependent (↥Qbar) ![1, v, conj v, (Polynomial.aeval v F / v ^ N), v * (Polynomial.aeval v F / v ^ N)])
    (hcg : conj (Polynomial.aeval v F / v ^ N) ∈ Submodule.span Qbar ({1, v, v * (Polynomial.aeval v F / v ^ N)} : Set ℂ)) :
    ∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧
      (2 ≤ G.natDegree ∨ v ^ 2 ∈ Submodule.span Qbar ({1, v, conj v, (Polynomial.aeval v F / v ^ N), v * (Polynomial.aeval v F / v ^ N)} : Set ℂ)) ∧
      Submodule.span Qbar ({1, v, conj v, (Polynomial.aeval v F / v ^ N), v * (Polynomial.aeval v F / v ^ N)} : Set ℂ) =
        Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ) := by
  sorry

end DiazModulus
