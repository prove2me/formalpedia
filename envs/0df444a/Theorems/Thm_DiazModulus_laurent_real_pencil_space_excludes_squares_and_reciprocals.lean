-- Prove2me | Theorems.Thm_DiazModulus_laurent_real_pencil_space_excludes_squares_and_reciprocals
-- name    : DiazModulus.laurent_real_pencil_space_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:22.039359+00:00
-- url     : https://prove2.me/theorems/e8931168-fed9-411b-b9c9-9b93486be31b
-- title:
--   For a real Laurent polynomial f in u/s of width k: if k ≥ 3, or k = 2 and f(−λ̄) ≠ 0, the real pencil space W(λ, f) contains none of u², ū², 1/(u − b)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$; with $v = u/s$, conjugation acts as $v \mapsto 1/v$ on coefficients). Let $\lambda \in \overline{\mathbb{Q}}$ with $|\lambda| = 1$, and let $f = \sum_{|j| \le k} c_j (u/s)^j$ with $c_j \in \overline{\mathbb{Q}}$, $c_{-j} = \bar c_j$ and $c_k \neq 0$ (so $f$ is real). Let $W(\lambda, f)$ be the \overline{\mathbb{Q}}-span of $1, u, \bar u, f, f/(s + \lambda u)$, and write $f(-\bar\lambda)$ for $\sum_j c_j(-\bar\lambda)^j$, the value at $v = -\bar\lambda$ (the pole of $f/(s + \lambda u)$). Suppose the five numbers are free, and that $k \geq 3$, or $k = 2$ and $f(-\bar\lambda) \neq 0$. Then $W(\lambda, f)$ contains none of $u^2$, $\bar u^2$ and $1/(u - b)$ for non-zero $b \in \overline{\mathbb{Q}}$.
--
--   **Proof.** Put $v = u/s$ (transcendental) and $P(X) = \sum_j c_jX^{j+k}$, so $v^kf = P(v)$, $\deg P = 2k$, $P(0) = c_{-k} \neq 0$. A membership $t = a_1 + a_2u + a_3\bar u + a_4f + a_5g$, multiplied by $N(v)\,s\,v^k(1 + \lambda v)$ ($N = 1$ for $u^2$ and $\bar u^2$, $N = sX - b$ for $1/(u - b)$), is an identity $T$ in \overline{\mathbb{Q}}$[X]$. Its degree forces $a_4 = 0$, except for $u^2$ at $k = 2$. At $X = 0$ it gives $N(0)(a_4s + a_5)c_{-k} = T(0)$, and $T(0) = 0$ except for $\bar u^2$ at $k = 2$. For $k = 2$, at $X = -\bar\lambda$ the factor $1 + \lambda X$ vanishes and $a_5P(-\bar\lambda) = 0$, with $P(-\bar\lambda) = \bar\lambda^2f(-\bar\lambda) \neq 0$. In every case $a_4 = a_5 = 0$, and $t \in \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ is refuted by a cubic in $u$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_real_pencil_space_excludes_squares_and_reciprocals
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (k : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j, c j ∈ Qbar) (hcs : ∀ j, c (-j) = conj (c j)) (hck : c k ≠ 0)
    (hk : 3 ≤ k ∨ (k = 2 ∧ (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (-conj lam) ^ j) ≠ 0)) (hind : LinearIndependent (↥Qbar) ![1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)]) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) := by
  sorry

end DiazModulus
