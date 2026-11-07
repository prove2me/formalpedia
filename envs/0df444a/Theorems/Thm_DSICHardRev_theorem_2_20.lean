-- Prove2me | Theorems.Thm_DSICHardRev_theorem_2_20
-- name    : DSICHardRev.theorem_2_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:39.429677+00:00
-- url     : https://prove2.me/theorems/0c6643b0-d076-448c-87d0-6874b19bc387
-- title:
--   Theorem 2.20 ([BH11]) — matroid rank functions with prescribed values on a set family
-- statement:
--   Let $b,d$ be integers with $20\le b\le d$, and let $\beta\ge 96d^3/b^2$ and $\lambda\in[4d/b,\,2^{b/10}]$ be integers. Then there exist sets $C_1,\dots,C_\lambda\subseteq[\beta]$ of size $d$ such that for every $x\in\{0,1\}^\lambda$ there is a matroid rank function $r_x:2^{[\beta]}\to\mathbb R_{\ge0}$ with
--
--   1. $r_x([\beta])\le d$;
--   2. $r_x(C_\ell)=d$ if $x_\ell=1$;
--   3. $r_x(C_\ell)=b$ if $x_\ell=0$.
--
--   The sets are chosen once, before $x$. This family, due to Balcan and Harvey, supplies the GS hard distribution of Proposition 3.2.
--
--   Differences from the source:
--   - encoding: parameters b, d, β, λ → natural numbers, with the bounds compared in ℝ; reason: b and d are values of an integer rank function, β and λ are sizes
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.4, p.10, Theorem 2.20

import Mathlib
import Definitions.Def_DSICHardRev_ValuationClasses

namespace DSICHardRev

/-- **Theorem 2.20 ([BH11])** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.4, p.10):
let `b, d` be parameters with `b ∈ [20, d]`, `β ≥ 96d³/b²` and `λ ∈ [4d/b, 2^{b/10}]`. Then there
exist sets `C_1, …, C_λ ⊆ [β]` of size `d` such that for all `x ∈ {0,1}^λ` there is a matroid rank
function `r_x : 2^{[β]} → ℝ₊` with `r_x([β]) ≤ d`, `r_x(C_ℓ) = d` if `x_ℓ = 1` and `r_x(C_ℓ) = b` if
`x_ℓ = 0`.

**Formalization Note.** `b, d, β, λ` are natural numbers (`b` and `d` are rank values, `β` and `λ`
sizes); the bounds on `β` and `λ` are compared in `ℝ`. `x ∈ {0,1}^λ` is `Fin λ → Fin 2`. The sets
are chosen before `x`, as printed. -/
theorem theorem_2_20 (b d β lam : ℕ) (hb : 20 ≤ b) (hbd : b ≤ d)
    (hβ : 96 * (d : ℝ) ^ 3 / (b : ℝ) ^ 2 ≤ β)
    (hlam₁ : 4 * (d : ℝ) / b ≤ lam) (hlam₂ : (lam : ℝ) ≤ (2 : ℝ) ^ ((b : ℝ) / 10)) :
    ∃ C : Fin lam → Finset (Fin β), (∀ l, (C l).card = d) ∧
      ∀ x : Fin lam → Fin 2, ∃ r : Finset (Fin β) → ℝ, IsMatroidRankFn r ∧
        r Finset.univ ≤ d ∧ (∀ l, x l = 1 → r (C l) = d) ∧ (∀ l, x l = 0 → r (C l) = b) := by sorry

end DSICHardRev
