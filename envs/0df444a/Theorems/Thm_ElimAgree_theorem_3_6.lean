-- Prove2me | Theorems.Thm_ElimAgree_theorem_3_6
-- name    : ElimAgree.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:20:14.271494+00:00
-- url     : https://prove2.me/theorems/935cf91a-182f-4af2-b03a-a6dafebc2281
-- title:
--   Theorem 3.6 — product rectangle deficit $\mu_I^{\otimes r}(R)\ge\lambda(R)-\frac{16}\ell J_\lambda(R)$
-- statement:
--   Let $\ell\ge1$, $N=4\ell-1$, let $\mu_D$ be uniform on pairs of disjoint $\ell$-subsets of $[N]$, $\mu_I$ uniform on pairs of $\ell$-subsets meeting in exactly one element, and $\lambda=\mu_D^{\otimes r}$ with marginals $\lambda_X,\lambda_Y$. For every $r\ge1$ and every rectangle $R=A\times B$ in the $r$-fold input space,
--   $$\mu_I^{\otimes r}(R)\ge\lambda(R)-\frac{16}{\ell}\,J_\lambda(R).$$
--
--   The constant $16/\ell$ does not depend on $r$.
--
--   Differences from the source:
--   - encoding: N = 4ℓ − 1 with ℓ-subsets (ℓ ≥ 1 implicit) → hypothesis 1 ≤ ℓ; reason: for ℓ = 0 there is no [N]
--   - encoding: rectangles in the r-fold input space of tuples of ℓ-subsets of [N] → rectangles of arbitrary tuples of subsets of [N]; the laws vanish off tuples of ℓ-subsets; reason: a rectangle of all subsets meets the support in a rectangle of ℓ-subsets with the same masses and marginals
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 3.6, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ElimAgree_deficit
import Definitions.Def_ElimAgree_muD

namespace ElimAgree

/-- Theorem 3.6 (Product rectangle deficit), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.9: with `N = 4ℓ − 1`, `µ_D` uniform on
pairs of disjoint `ℓ`-subsets of `[N]`, `µ_I` uniform on pairs of `ℓ`-subsets meeting in exactly
one element and `λ = µ_D^{⊗r}`, for every `r ≥ 1` and every rectangle `R = A × B` in the
`r`-fold input space, `µ_I^{⊗r}(R) ≥ λ(R) − (16/ℓ) J_λ(R)`.

**Formalization Note.** The `r`-fold input space of each party is all `r`-tuples of subsets of
`[N]`; the laws live on tuples of `ℓ`-subsets, and `A`, `B` are arbitrary. `J_λ` uses `λ`'s own
marginals. `1 ≤ ℓ` is the setting of §3.3 (`N = 4ℓ − 1`). -/
theorem theorem_3_6 (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) (A B : Finset (Fin r → Nset ℓ)) :
    lawRect (muIpow ℓ r) A B ≥
      lawRect (lamD ℓ r) A B - 16 / (ℓ : ℝ) * deficit (lamD ℓ r) A B := by sorry

end ElimAgree
