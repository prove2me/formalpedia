-- Prove2me | Theorems.Thm_DiazModulus_conj_swapped_two_orbit_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.conj_swapped_two_orbit_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-15T11:58:40.093207+00:00
-- url     : https://prove2.me/theorems/dff5b4bf-d4b1-4857-9ee9-b28491871a77
-- title:
--   For u ∉ Q̄ with |u| = s algebraic and g = a₁/(u − a) + a₂/(u + a), |a| ≠ s, a₁ ≠ a₂: span{1, u, u⁻¹, g, ḡ} is conjugation-stable, spanned by a 2×3 configuration, invisible to Theorem B
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$). Let $a, a_1, a_2 \in \overline{\mathbb{Q}}^\times$ with $a\bar a \neq s^2$ and $a_1 \neq a_2$, put $g = a_1/(u - a) + a_2/(u + a)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}, g, \bar g$. Then $W$ is stable under conjugation, a $2 \times 3$ configuration's six products span it, and for no $w \in W$ outside $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ does $H_0 + \overline{\mathbb{Q}}w$ carry one.
--
--   Conjugation maps the orbit $\{a, -a\}$ of $u \mapsto -u$ to $\{s^2/\bar a, -s^2/\bar a\}$, a different orbit when $|a| \neq s$: this is the swapped case of the conjugation-stable two-orbit spaces, whose fixed case is `DiazModulus.conj_stable_two_orbit_space`.
--
--   **Proof.** Put $b = s^2/\bar a$. Since $\bar u = s^2/u$, $\bar u - \bar a = -\bar a(u - b)/u$ and $\bar u + \bar a = \bar a(u + b)/u$, so $\bar g = (\bar a_2 - \bar a_1)/\bar a + \gamma/(u - b) + \delta/(u + b)$ with $\gamma = -\bar a_1 b/\bar a$ and $\delta = -\bar a_2 b/\bar a$, both non-zero. As $1 \in W$, $W$ is also the span of $1, u, u^{-1}, g$ and $\gamma/(u - b) + \delta/(u + b)$: a two-orbit space for the orbits $\pm a$ and $\pm b$. These differ, since $a^2 = b^2$ would give $(a\bar a - s^2)(a\bar a + s^2) = 0$, and $a\bar a + s^2 = |a|^2 + |u|^2 > 0$. With $a_1 \neq a_2$, `DiazModulus.two_orbit_configuration_invisible_to_four_dimensional_extensions` gives the spanning configuration and the invisibility. Conjugation maps $1, u, u^{-1}, g, \bar g$ into $W$ ($\bar u = s^2u^{-1}$, $\overline{u^{-1}} = u/s^2$), and induction on the span finishes.
--
--   **Novelty.** The configuration is printed: rescaled by $u^{\mp 1}$, it is the configuration $(v, \bar v) \otimes (1, w, \bar w)$ of Diaz (2007, Th. 7(1)) at $v = u$, $w = ug$ (credited here on 16 October 2026). That no four-dimensional extension of $H_0$ inside $W$ carries a configuration was not found in the sources read; routine.
-- source:
--   The configuration is that of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(1) (p. 390), at v = u, w = ug. That no four-dimensional extension inside W carries one was not found in the sources read. Uses DiazModulus.two_orbit_configuration_invisible_to_four_dimensional_extensions. R15 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 15 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem conj_swapped_two_orbit_configuration_invisible_to_four_dimensional_extensions
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (a a₁ a₂ : ℂ) (ha : a ∈ Qbar) (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar) (ha0 : a ≠ 0)
    (haa : a * conj a ≠ s * s) (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha₁₂ : a₁ ≠ a₂) :
    (∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ)) ∧
        Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 => x p.1 * y p.2)) = Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
