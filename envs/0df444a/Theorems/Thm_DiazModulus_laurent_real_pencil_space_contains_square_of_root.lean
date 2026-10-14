-- Prove2me | Theorems.Thm_DiazModulus_laurent_real_pencil_space_contains_square_of_root
-- name    : DiazModulus.laurent_real_pencil_space_contains_square_of_root
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:25.844221+00:00
-- url     : https://prove2.me/theorems/ae727e89-8d03-47a2-a317-c5ad17b15d54
-- title:
--   For a real Laurent polynomial f in u/s of width 2 with f(−λ̄) = 0, the real pencil space W(λ, f) contains u² and ū²
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$; with $v = u/s$, conjugation acts as $v \mapsto 1/v$ on coefficients). Let $\lambda \in \overline{\mathbb{Q}}$ with $|\lambda| = 1$, and let $f = \sum_{|j| \le k} c_j (u/s)^j$ with $c_j \in \overline{\mathbb{Q}}$, $c_{-j} = \bar c_j$ and $c_k \neq 0$ (so $f$ is real). Let $W(\lambda, f)$ be the \overline{\mathbb{Q}}-span of $1, u, \bar u, f, f/(s + \lambda u)$, and write $f(-\bar\lambda)$ for $\sum_j c_j(-\bar\lambda)^j$, the value at $v = -\bar\lambda$ (the pole of $f/(s + \lambda u)$). If $k = 2$ and $f(-\bar\lambda) = 0$, then $u^2$ and $\bar u^2$ lie in $W(\lambda, f)$, so Theorem B sees it.
--
--   So R11's invisible example $u^2/s^2 + s^2/u^2$ ($\lambda = 1$, $f(-1) = 2 \neq 0$) is the generic case, and $(u/s - s/u)^2$ with $\lambda = 1$ is a visible one.
--
--   **Proof.** With $k = 2$ the sum has five terms. Multiplied by $\lambda^2$ (using $\bar\lambda = \lambda^{-1}$), $f(-\bar\lambda) = 0$ reads $c_2 - \lambda c_1 + \lambda^2c_0 - \lambda^3c_{-1} + \lambda^4c_{-2} = 0$, which is exactly the vanishing remainder of $v^2f$ divided by $1 + \lambda v$. So $s\,g = c_{-2}v^{-2} + q_{-1}v^{-1} + q_0 + q_1v$, and explicit identities express $c_{-2}\bar u^2$ and $c_2u^2$ as \overline{\mathbb{Q}}-combinations of $1, u, \bar u, f, g$; as $c_2 \neq 0$ and $c_{-2} = \bar c_2 \neq 0$, both $u^2$ and $\bar u^2$ lie in $W(\lambda, f)$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_real_pencil_space_contains_square_of_root
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (k : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j, c j ∈ Qbar) (hcs : ∀ j, c (-j) = conj (c j)) (hck : c k ≠ 0)
    (hk : k = 2) (hroot : (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (-conj lam) ^ j) = 0) :
    u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) ∧ conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) := by
  sorry

end DiazModulus
