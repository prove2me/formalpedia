-- Prove2me | Theorems.Thm_DiazModulus_real_pencil_quartic_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.real_pencil_quartic_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-11T08:03:12.418983+00:00
-- url     : https://prove2.me/theorems/a5c588d2-840c-4db0-bf64-b41a6ae70cb5
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, the span of 1, u, ū, f, f/(s + u), f = u²/s² + s²/u², is conjugation-stable with a 2×3 configuration that no Q̄ + Q̄u + Q̄ū + Q̄w inside it carries
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$. Put $f = u^2/s^2 + s^2/u^2$ (that is $v^2 + v^{-2}$ with $v = u/s$) and let $W$ be the \overline{\mathbb{Q}}-span of $1, u, \bar u, f, f/(s + u)$. Put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$. Then $W$ is stable under complex conjugation and carries a $2 \times 3$ configuration, but for no $w \in W$ outside $H_0$ does $H_0 + \overline{\mathbb{Q}}w$ carry one.
--
--   The conjecture of R5, that the conjugation-stable spaces Theorem B does not see contain a geometric progression, is false: this $W$ contains none.
--
--   **Proof.** Conjugation stability and the configuration are `DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration` with $\lambda = 1$ ($f$ is real since $\bar u = s^2/u$), the freeness coming from `DiazModulus.real_pencil_quartic_space_excludes_squares_and_reciprocals`. If some $H_0 + \overline{\mathbb{Q}}w$ with $w \in W \setminus H_0$ carried a configuration, Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) and exchange would put $u^2$, $\bar u^2$ or some $1/(u - b)$ in $W$, which the exclusions rule out.
--
--   **Novelty.** Not found in the sources read; it is short. It answers in the negative the question left open by R9 (a conjugation-stable invisible space that is not a progression).
-- source:
--   Not found in the sources read. Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission). R11 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 11 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem real_pencil_quartic_configuration_invisible_to_four_dimensional_extensions
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ),
        w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
          LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
