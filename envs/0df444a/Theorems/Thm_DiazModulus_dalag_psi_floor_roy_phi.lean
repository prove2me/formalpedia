-- Prove2me | Theorems.Thm_DiazModulus_dalag_psi_floor_roy_phi
-- name    : DiazModulus.dalag_psi_floor_roy_phi
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:30.836795+00:00
-- url     : https://prove2.me/theorems/924a0b97-f9d8-4438-be5c-68a0c5b62626
-- title:
--   DALAG's Ψ is the integer part of Roy's maximum: for 0 < n < d, every decomposition (n, d) = Σ (nᵢ, dᵢ) has Σ nᵢdᵢ/(dᵢ − nᵢ) < Ψ(n, d) + 1, and some decomposition has it ≥ Ψ(n, d)
-- statement:
--   A *decomposition* of a pair $(n, d)$ of natural numbers is a finite list $(n_1, d_1), \dots, (n_k, d_k)$ of pairs of natural numbers with $0 < n_i < d_i$ for every $i$, $\sum_i n_i = n$ and $\sum_i d_i = d$ (the empty list, $k = 0$, decomposes $(0, 0)$ only). The *value* of a decomposition $(n_1, d_1), \dots, (n_k, d_k)$ is the rational number $\sum_{i=1}^k n_i d_i/(d_i - n_i)$.
--
--   DALAG's function $\Psi$ is given by a table (DALAG, §11.5, p. 394). Here, for natural numbers $a, b$, $\Psi(a, b)$ is defined by the following cases, taken in this order: $\Psi(a, b) = 0$ if $a = 0$; else $\Psi(a, b) = 1$ if $a = 1$ and $b \ge 3$; else $a(a - 1) + 1$ if $a \ge 2$ and $a + 3 \le b$; else $a(a - 1) + 2$ if $a \ge 2$ and $a + 2 = b$; else $a(a + 1)$ if $a + 1 = b$; and $0$ in every remaining case (these are $a \ge 1$ with $b \le a$, outside the table). For $0 < a < b$ the four middle cases are the four rows of the printed table, and $\Psi(0, b) = 0$ for every $b$.
--
--   Let $0 < n < d$. Then every decomposition of $(n, d)$ has value $< \Psi(n, d) + 1$, and some decomposition of $(n, d)$ has value $\ge \Psi(n, d)$. So $\Psi(n, d)$ is the integer part of Roy's $\varphi(n, d)$, the greatest value of a decomposition of $(n, d)$ (Roy 1992, pp. 38–40).
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 11.15 (p. 398), in its Ψ form: the table of Ψ (p. 394) compared row by row with Roy's closed form (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Lemma, p. 40). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_psi_floor_roy_phi {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    let Ψ : ℕ → ℕ → ℕ := fun a b =>
      if a = 0 then 0
      else if a = 1 ∧ 3 ≤ b then 1
      else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
      else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
      else if a + 1 = b then a * (a + 1)
      else 0
    (∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) → (D.map Prod.fst).sum = n →
        (D.map Prod.snd).sum = d →
        (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum < (Ψ n d : ℚ) + 1) ∧
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧ (D.map Prod.fst).sum = n ∧
      (D.map Prod.snd).sum = d ∧
      (Ψ n d : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  sorry

end DiazModulus
