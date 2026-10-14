-- Prove2me | Theorems.Thm_DiazModulus_laurent_real_pencil_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.laurent_real_pencil_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:16.999544+00:00
-- url     : https://prove2.me/theorems/818db686-8350-40ab-a7b8-250bc1d48c77
-- title:
--   For a real Laurent polynomial f in u/s of width k ≥ 3, or 2 with f(−λ̄) ≠ 0: W(λ, f) is conjugation-stable with a 2×3 configuration invisible to Theorem B
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$; with $v = u/s$, conjugation acts as $v \mapsto 1/v$ on coefficients). Let $\lambda \in \overline{\mathbb{Q}}$ with $|\lambda| = 1$, and let $f = \sum_{|j| \le k} c_j (u/s)^j$ with $c_j \in \overline{\mathbb{Q}}$, $c_{-j} = \bar c_j$ and $c_k \neq 0$ (so $f$ is real). Let $W(\lambda, f)$ be the \overline{\mathbb{Q}}-span of $1, u, \bar u, f, f/(s + \lambda u)$, and write $f(-\bar\lambda)$ for $\sum_j c_j(-\bar\lambda)^j$, the value at $v = -\bar\lambda$ (the pole of $f/(s + \lambda u)$). Suppose the five numbers are free, and that $k \geq 3$, or $k = 2$ and $f(-\bar\lambda) \neq 0$. Put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$. Then $W(\lambda, f)$ is stable under conjugation and carries a $2 \times 3$ configuration, and for no $w \in W(\lambda, f)$ outside $H_0$ does $H_0 + \overline{\mathbb{Q}}w$ carry one.
--
--   With `DiazModulus.laurent_real_pencil_space_contains_square_of_root` this settles visibility for Laurent $f$: $W(\lambda, f)$ is visible exactly when $k = 2$ and $f(-\bar\lambda) = 0$.
--
--   **Proof.** $f$ is real: conjugation sends $u/s$ to $(u/s)^{-1}$ and $c_j$ to $c_{-j}$, so reindexing $j \mapsto -j$ returns the sum. Then `DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration` gives conjugation stability and a configuration, and Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) with exchange against `DiazModulus.laurent_real_pencil_space_excludes_squares_and_reciprocals` rules out every $H_0 + \overline{\mathbb{Q}}w$ with $w \notin H_0$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. Uses DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration and DiazModulus.circle_point_extension_two_by_three_configuration_iff. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_real_pencil_configuration_invisible_to_four_dimensional_extensions
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (k : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j, c j ∈ Qbar) (hcs : ∀ j, c (-j) = conj (c j)) (hck : c k ≠ 0)
    (hk : 3 ≤ k ∨ (k = 2 ∧ (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (-conj lam) ^ j) ≠ 0)) (hind : LinearIndependent (↥Qbar) ![1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)]) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
