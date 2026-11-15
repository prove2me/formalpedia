-- Prove2me | Theorems.Thm_DiazModulus_roy_lemma_phi
-- name    : DiazModulus.roy_lemma_phi
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:56.143165+00:00
-- url     : https://prove2.me/theorems/057fca9b-674e-4315-a7d3-7777769c0384
-- title:
--   Roy 1992, Lemma p. 40: for 0 < n < d, the maximum of Σ nᵢdᵢ/(dᵢ − nᵢ) over (n, d) = Σ (nᵢ, dᵢ) with 0 < nᵢ < dᵢ is nd/(d − n) if n = 1 or d − n = 1, else (d − n)/(d − n − 1) + (n − 1)n
-- statement:
--   A *decomposition* of a pair $(n, d)$ of natural numbers is a finite list $(n_1, d_1), \dots, (n_k, d_k)$ of pairs of natural numbers with $0 < n_i < d_i$ for every $i$, $\sum_i n_i = n$ and $\sum_i d_i = d$ (the empty list, $k = 0$, decomposes $(0, 0)$ only). The *value* of a decomposition $(n_1, d_1), \dots, (n_k, d_k)$ is the rational number $\sum_{i=1}^k n_i d_i/(d_i - n_i)$.
--
--   Let $0 < n < d$, and let $F(n, d) = nd/(d - n)$ if $n = 1$ or $d - n = 1$, and $F(n, d) = (d - n)/(d - n - 1) + (n - 1)\,n$ otherwise. Then $F(n, d)$ is the greatest value of a decomposition of $(n, d)$: some decomposition of $(n, d)$ has value $F(n, d)$, and every decomposition of $(n, d)$ has value at most $F(n, d)$.
--
--   Roy's $\varphi(n, d)$ is this greatest value (Roy 1992, pp. 38–39). Roy's Lemma gives it as $\varphi(1, d - n) + \varphi(n - 1, n)$ when $n \ge 2$ and $d - n \ge 2$; by the case $n = 1$ or $d - n = 1$, $\varphi(1, d - n) = (d - n)/(d - n - 1)$ and $\varphi(n - 1, n) = (n - 1)\,n$, so the two forms agree.
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Lemma (p. 40; proof pp. 40–41), with the second value in closed form: Roy writes it φ(1, d − n) + φ(n − 1, n), which is (d − n)/(d − n − 1) + (n − 1)n. Roy's printed proof of his Lemma (p. 41) concludes 'k = 2' without excluding several parts (1, 1). For example, the decomposition [(1, 2), (1, 1), (1, 1)] of (n, δ) = (3, 4), in Roy's pairs (nᵢ, δᵢ) with δᵢ = dᵢ − nᵢ, meets the conditions he states, with k = 3, and one more exchange repairs it: (a, 1), (1, b), (1, 1) → (a + 1, 1), (1, b + 1), for a, b ≥ 1, raises Σ nᵢ²/δᵢ. The Lean proof uses a different route: superadditivity of the closed form (DiazModulus.roy_phi_closed_form_superadd). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_lemma_phi {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    IsGreatest
      {x : ℚ | ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
        (D.map Prod.fst).sum = n ∧ (D.map Prod.snd).sum = d ∧
        x = (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum}
      (if n = 1 ∨ d - n = 1 then ((n : ℚ) * d) / ((d : ℚ) - n)
        else ((d : ℚ) - n) / ((d : ℚ) - n - 1) + ((n : ℚ) - 1) * n) := by
  sorry

end DiazModulus
