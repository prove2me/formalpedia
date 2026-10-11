-- Prove2me | Theorems.Thm_DiazModulus_conj_stable_real_pencil_space_carries_two_by_three_configuration
-- name    : DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-11T08:03:43.511996+00:00
-- url     : https://prove2.me/theorems/e9964520-a9f1-44f5-b162-795fd27d47a7
-- title:
--   For u ∉ Q̄, real algebraic s with s² = uū, |λ| = 1 and real f, the span of 1, u, ū, f, f/(s + λu) is stable under conjugation and carries a 2×3 configuration
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $s = \pm|u|$). Let $\lambda \in \overline{\mathbb{Q}}$ with $|\lambda| = 1$, let $f \in \mathbb{C}$ be real, put $g = f/(s + \lambda u)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, f, g$. Suppose these five numbers are free over $\overline{\mathbb{Q}}$. Then $W$ is stable under complex conjugation, and the products of $(1, u)$ and $(u^{-1}, 1, g)$, two free families, all lie in $W$.
--
--   This is the family $W(\lambda, f)$ of the research notes: the conjugation-stable five-dimensional spaces containing $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ that carry a $2 \times 3$ configuration $(1, u) \otimes (y_1, y_2, y_3)$ (after rescaling). It is not a geometric progression in general, so it is a separate case from the involution spaces of R9.
--
--   **Proof.** $u \neq 0$, $s \neq 0$ and $s + \lambda u \neq 0$ since $u$ is transcendental; $\bar u = s^2/u$. Using $\lambda\bar\lambda = 1$, $\bar g = f/s - g$ and $ug = (f - sg)/\lambda$, so conjugation maps each generator into $W$, and $x = (1, u)$, $y = (u^{-1}, 1, g)$ has its six products $u^{-1} = \bar u/s^2, 1, g, u, 1, ug$ in $W$. Both families are free: $u \notin \overline{\mathbb{Q}}$, and $(u^{-1}, 1, g)$ is a rescaled subfamily of the five free generators.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R11 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 11 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem conj_stable_real_pencil_space_carries_two_by_three_configuration
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (f : ℂ) (hf : conj f = f)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, f, f / (s + lam * u)]) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ)) ∧
      ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ) := by
  sorry

end DiazModulus
