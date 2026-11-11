-- Prove2me | Theorems.Thm_CubicPermFPRAS_proposition_37
-- name    : CubicPermFPRAS.proposition_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:43.25+00:00
-- url     : https://prove2.me/theorems/52d790de-26fb-4648-854a-572e62ad5548
-- title:
--   Proposition 37, p.38 — $F(a)=B(\mathcal P)\prod_j(a+\rho_j)$ with $\rho_j>0$
-- statement:
--   Let $B$ be an $n\times n$ matrix with positive entries and $F(a)=\sum_{M}a^{|M|}B(M)$ the sum over all matchings of $K_{n,n}$. There exist positive numbers $\rho_1,\dots,\rho_n$, depending only on $B$, such that
--   $$F(a)=B(\mathcal P)\prod_{j=1}^n(a+\rho_j)\qquad\text{for every real }a.$$
--
--   This real-rooted factorization (from the Heilmann–Lieb theorem) drives the partition-function comparisons of Lemmas 38 and 42 and the warm-start step of Lemma 10.
--
--   Differences from the source:
--   - generalization: $B$ the rescaled matrix of Eq. (10) → every matrix $B$ with positive entries; reason: the rescaled matrix has positive entries; the proof uses only positivity
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Proposition 37, p.38 (PDF 40)

import Mathlib
import Definitions.Def_CubicPermFPRAS_nuAux

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Proposition 37** (real-rooted factorization of the matching polynomial), p.38 (PDF 40),
X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…).

There exist positive numbers `ρ₁, …, ρ_n`, depending only on `B` and independent of `a`, such
that `F(a) = B(P) ∏_{j=1}^n (a + ρ_j)` for every `a`, where
`F(a) = ∑_{M a matching} a^{|M|} B(M)`.

**Formalization Note.** Stated for every matrix `B` with positive entries (the paper applies it
to the rescaled matrix of Eq. (10), which is positive); the proof (Heilmann–Lieb) uses only
positivity. "For every `a`" is every real `a`. -/
theorem proposition_37 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ u v, 0 < B u v) :
    ∃ ρ : Fin n → ℝ, (∀ j, 0 < ρ j) ∧
      ∀ a : ℝ, Fpoly B a = familyWeight B (PSet n) * ∏ j, (a + ρ j) := by sorry

end CubicPermFPRAS
