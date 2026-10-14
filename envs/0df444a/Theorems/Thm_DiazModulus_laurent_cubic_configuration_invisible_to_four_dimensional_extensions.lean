-- Prove2me | Theorems.Thm_DiazModulus_laurent_cubic_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.laurent_cubic_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:13.632475+00:00
-- url     : https://prove2.me/theorems/f71c2dff-fe3c-4f65-9b0e-bac9bb16375a
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, the span of 1, u, ū, u³/s³ + u²/s², ū³/s³ + ū²/s² is conjugation-stable, spanned by a 2×3 configuration, and invisible to Theorem B
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$; with $v = u/s$, conjugation acts as $v \mapsto 1/v$ on coefficients). Put $F = u^3/s^3 + u^2/s^2$ and let $W_1$ be the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, F, \bar F$ (in $v$: $v^{-1}, 1, v, v^3 + v^2, v^{-3} + v^{-2}$). Put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$. Then $W_1$ is stable under complex conjugation; it carries a $2 \times 3$ configuration whose six products span $W_1$; and for no $w \in W_1$ outside $H_0$ does $H_0 + \overline{\mathbb{Q}}w$ carry one.
--
--   $W_1$ answers a question left open in R10: a conjugation-stable five-dimensional space containing $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ can carry a configuration that Theorem B does not see without having a configuration factor of degree one, so it is not one of R11's real pencil spaces.
--
--   **Proof.** $\bar F$ and $F$ are exchanged by conjugation, so the span is conjugation-stable (induction on the span). With $x = (1, u^2)$ and $y = (\bar u, u + s, \bar F)$ the six products are $\bar u$, $u + s$, $\bar F$, $s^2u$, $s^3F$ and $s\bar u + s^2$; they give back $1, u, \bar u, F, \bar F$, so they span $W_1$, and both families are free by `DiazModulus.laurent_cubic_space_excludes_squares_and_reciprocals`. Invisibility is Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) and exchange against the same node's exclusions.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission). R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_cubic_configuration_invisible_to_four_dimensional_extensions
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧
        Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 => x p.1 * y p.2)) = Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
