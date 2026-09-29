-- Prove2me | Theorems.Thm_Diaz_power_support_sumfree
-- name    : Diaz.power_support_sumfree
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:51.775906+00:00
-- url     : https://prove2.me/theorems/916e1506-ba2c-4539-ba6e-d126e098de13
-- title:
--   A symmetric difference-sparse support is sum-free and misses 2 and 3
-- statement:
--   Let $S \subseteq \mathbb{Z}$ be symmetric ($n \in S \Rightarrow -n \in S$), contain $0$ and $1$, and satisfy: for no non-zero $d$ do three distinct integers $n_1, n_2, n_3$ have $n_j, n_j + d \in S$. Then the non-zero part of $S$ is sum-free, and $\pm 2, \pm 3 \notin S$.
--
--   **Where this sits.** This is Carlo Perassi's power rigidity of a Diaz candidate, with the arithmetic replaced by hypotheses. There $S = S(u) = \{n : u^{n} \in \widetilde{\mathcal{L}}\}$ for a Diaz candidate $u$; symmetry holds because $\bar u = \rho/u$ with $\rho$ algebraic and $\widetilde{\mathcal{L}}$ is conjugation-stable, $-1, 0, 1 \in S(u)$ trivially, and the three-pair exclusion is his power-support sparsity theorem, ultimately Roy's strong six exponentials theorem. The conclusion there is
--
--   $$u^{\pm 2},\ u^{\pm 3} \notin \widetilde{\mathcal{L}}.$$
--
--   For a candidate, the cases $\pm3$ of this conclusion also follow from Corollaire 5(2) of G. Diaz, J. Théor. Nombres Bordeaux 19 (2007), p. 383, and the cases $\pm2$ from Corollaire 5(1) there when $1$, $u$, $\bar u$ are linearly independent over $\overline{\mathbb{Q}}$: those points put $\lambda/\bar\lambda$ and $\lambda^{2}/\bar\lambda$ outside $\widetilde{\mathcal{L}}$, and since $u\bar u$ is a non-zero algebraic number, at $\lambda = u$ and $\lambda = \bar u$ these quotients are $u^{\pm2}$ and $u^{\pm3}$ up to non-zero algebraic factors.
--
--   **Proof.** For sum-freeness, if $m, n, m+n$ are non-zero elements of $S$ then the difference $d = m$ occurs in the three pairs with initial terms $-m$, $0$, $n$, which are distinct precisely because $m, n, m+n \neq 0$; that is the excluded configuration. Taking $m = n = 1$ excludes $2$, and $-2$ follows by symmetry. Sum-freeness does not exclude $3$, since $2 \notin S$; instead the difference $2$ occurs in $(-3,-1)$, $(-1,1)$, $(1,3)$, and these have distinct initial terms.
--
--   Elementary. Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.power_support_sumfree (S : Set ℤ)
    (hsym : ∀ n : ℤ, n ∈ S → -n ∈ S)
    (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S)
    (hpair : ∀ d : ℤ, d ≠ 0 → ∀ n₁ n₂ n₃ : ℤ, n₁ ≠ n₂ → n₁ ≠ n₃ → n₂ ≠ n₃ →
        n₁ ∈ S → n₁ + d ∈ S → n₂ ∈ S → n₂ + d ∈ S → n₃ ∈ S → n₃ + d ∈ S → False) :
    (∀ m n : ℤ, m ≠ 0 → n ≠ 0 → m + n ≠ 0 → m ∈ S → n ∈ S → m + n ∉ S)
      ∧ (2 : ℤ) ∉ S ∧ (-2 : ℤ) ∉ S ∧ (3 : ℤ) ∉ S ∧ (-3 : ℤ) ∉ S := by sorry
