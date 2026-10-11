-- Prove2me | Theorems.Thm_DiazModulus_conj_equivariant_degree_one_space_eq_real_pencil_space
-- name    : DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-11T08:03:16.737339+00:00
-- url     : https://prove2.me/theorems/52da0e34-a456-43ea-aa23-27c31ae95cbe
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū: if 1, u, ū, g, ug are free and ḡ ∈ Q̄ + Q̄u + Q̄ug, the span is Q̄ + Q̄u + Q̄ū + Q̄f + Q̄f/(s + λu) with |λ| = 1, f real
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$. Let $g \in \mathbb{C}$ be such that $1, u, \bar u, g, ug$ are free over $\overline{\mathbb{Q}}$ and $\bar g \in \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}ug$. Then there are $\lambda \in \overline{\mathbb{Q}}$ with $\lambda\bar\lambda = 1$ and a real $f$ such that $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}g + \overline{\mathbb{Q}}ug = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}f + \overline{\mathbb{Q}}f/(s + \lambda u)$.
--
--   The spaces $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}g + \overline{\mathbb{Q}}ug$ are those that carry the configuration $(1, u) \otimes (u^{-1}, 1, g)$. The hypothesis on $\bar g$ says that conjugation maps this configuration to one of the same shape. With `DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration` it shows that the family $W(\lambda, f)$ is all of them.
--
--   **Proof.** Write $\bar g = a + bu + c\,ug$. Conjugating and substituting $\bar u = s^2/u$ gives $(1 - c\bar c s^2)g \in \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\bar u$, so by freeness $c\bar cs^2 = 1$, $\bar a = -\bar c s^2 b$ and $\bar b = -\bar c a$. With $q = a/(cs^2)$, $g' = g + q\bar u$ satisfies $\bar{g'} = c\,ug'$. Put $\lambda = cs$, so $|\lambda| = 1$, and $f = g'(s + \lambda u)$; then $\bar f = f$ and $f/(s + \lambda u) = g'$. The two spans agree generator by generator, using $ug' = ug + qs^2$ and $f = sg' + \lambda ug'$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R11 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 11 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem conj_equivariant_degree_one_space_eq_real_pencil_space
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) (g : ℂ)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g])
    (hcg : conj g ∈ Submodule.span Qbar ({1, u, u * g} : Set ℂ)) :
    ∃ lam f : ℂ, lam ∈ Qbar ∧ lam * conj lam = 1 ∧ conj f = f ∧
      Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) = Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ) := by
  sorry

end DiazModulus
