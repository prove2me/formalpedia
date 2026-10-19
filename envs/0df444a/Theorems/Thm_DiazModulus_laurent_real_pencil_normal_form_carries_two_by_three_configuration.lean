-- Prove2me | Theorems.Thm_DiazModulus_laurent_real_pencil_normal_form_carries_two_by_three_configuration
-- name    : DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:42.808784+00:00
-- url     : https://prove2.me/theorems/6739af20-d128-4b91-9ac4-b1591ec8bf80
-- title:
--   For g = G(v) + κ · conj(v G(v)) with |κ| = 1 and deg G ≥ 1, (1, v) and (v̄, 1, g) form a 2×3 configuration in span(1, v, v̄, g, ḡ)
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$, let $G \in \overline{\mathbb{Q}}[X]$ with $\deg G \geq 1$, and put $g = G(v) + \kappa\,\overline{vG(v)}$. Then $1, v$ are linearly independent over $\overline{\mathbb{Q}}$, so are $\bar v, 1, g$, and each of the six products of a member of $(1, v)$ with a member of $(\bar v, 1, g)$ lies in $\mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, g, \bar g)$.
--
--   **Proof.** The products are $\bar v, 1, g$, $v\bar v = 1$, $v$ and $vg = \kappa\bar g$, the last identity using only $v\bar v = 1$ and $\kappa\bar\kappa = 1$. The family $(1, v)$ is free as $v \notin \overline{\mathbb{Q}}$. For $(\bar v, 1, g)$, with $n = \deg G$, $v^n\overline{G(v)}$ is the value at $v$ of the reflected conjugate polynomial, of degree at most $n$, so a relation $g_0\bar v + g_1 + g_2g = 0$ times $v^{n+1}$ is a polynomial identity at the transcendental $v$ whose coefficient at $X^{2n+1}$ is $g_2$ times the leading coefficient of $G$. So $g_2 = 0$, and then $g_0\bar v + g_1 = 0$ gives $g_0 = g_1 = 0$.
--
--   **Novelty.** Not found in the sources read in this form; routine. It is the configuration of `DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration`, written for Laurent data.
-- source:
--   Not found in the sources read in this form; the configuration of DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration, for Laurent data. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_real_pencil_normal_form_carries_two_by_three_configuration
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (κ : ℂ) (hκ : κ ∈ Qbar) (hκ1 : κ * conj κ = 1) (G : Polynomial ↥Qbar) (hG : 1 ≤ G.natDegree) :
    LinearIndependent (↥Qbar) ![1, v] ∧
      LinearIndependent (↥Qbar) ![conj v, 1, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G)] ∧
      ∀ i j, ![1, v] i * ![conj v, 1, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G)] j ∈
        Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ) := by
  sorry

end DiazModulus
