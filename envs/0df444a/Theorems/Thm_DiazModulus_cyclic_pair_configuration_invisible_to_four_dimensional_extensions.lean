-- Prove2me | Theorems.Thm_DiazModulus_cyclic_pair_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.cyclic_pair_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-15T11:58:39.681288+00:00
-- url     : https://prove2.me/theorems/c5f1b34c-b54c-4dd5-92a5-f15bf59cfcff
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, the cyclic space with double poles at ±s is conjugation-stable, spanned by a 2×3 configuration and invisible to Theorem B
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$). With $v = u/s$, put $G_1 = 1/(v - 1) + 2/(v + 1)$ and $G_2 = 1/(v - 1)^2 + 1/(v - 1) - 2/(v + 1)^2 + 2/(v + 1)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, G_1, G_2$ (poles at $u = \pm s$, each a double pole). Then $W$ is stable under conjugation, the six products of $(1, u^2)$ and $(\bar u, G_1, G_2)$ span it, and for no $w \in W$ outside $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ does $H_0 + \overline{\mathbb{Q}}w$ carry a configuration.
--
--   $W$ is the cyclic member of the classification of conjugation-stable invisible spaces with a configuration factor of degree two (research notes R12, Q1.7): the factor $(1, u^2)$ acts on $G_1, G_2$ modulo $H_0$ as a Jordan block, where R14's two-orbit spaces have two eigenvalues.
--
--   **Proof.** Write $\bar u = s^2/u$. Then $\bar G_1 = 1 - G_1$ and $\bar G_2 = G_2$ (clear denominators and reduce modulo $\bar u u = s^2$), so conjugation maps the five generators into $W$, and induction on the span finishes. The six products of $x = (1, u^2)$ and $y = (\bar u, G_1, G_2)$ are $\bar u$, $G_1$, $G_2$, $u^2\bar u = s^2u$, $u^2G_1 = 3su - s^2 + s^2G_1$ and $u^2G_2 = s^2G_2 + 3su - 2s^2 + 2s^2G_1$: all in $W$, and they give back $u = u^2\bar u/s^2$ and $1 = 3u/s + G_1 - u^2G_1/s^2$, so they span $W$. The pair $x$ is free as $u^2 \notin W$, and $y$ is free as the five generators are, both by `DiazModulus.cyclic_pair_space_excludes_squares_and_reciprocals`. Invisibility: if $H_0 + \overline{\mathbb{Q}}w$ carries a configuration for some $w \in W$ outside $H_0$, Theorem B puts $w$ in $H_0 + \overline{\mathbb{Q}}t$ with $t = u^2$, $\bar u^2$ or $(u - e)^{-1}$; by exchange $t \in H_0 + \overline{\mathbb{Q}}w \subseteq W$, which the same node excludes.
--
--   **Novelty.** The configuration is printed: rescaled by $u^{\mp 1}$, it is the configuration $(v, \bar v) \otimes (1, w, \bar w)$ of Diaz (2007, Th. 7(1)) at $v = u$, $w = uG_2$ (credited here on 16 October 2026). That no four-dimensional extension of $H_0$ inside $W$ carries a configuration was not found in the sources read; routine.
-- source:
--   The configuration is that of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(1) (p. 390), at v = u, w = uG₂. That no four-dimensional extension inside W carries one was not found in the sources read. Uses DiazModulus.cyclic_pair_space_excludes_squares_and_reciprocals and DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission). R15 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 15 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cyclic_pair_configuration_invisible_to_four_dimensional_extensions
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧
        Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 => x p.1 * y p.2)) = Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
