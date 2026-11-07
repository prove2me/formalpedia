-- Prove2me | Theorems.Thm_AlgoPFR_theorem_3_5_entropic_pfr
-- name    : AlgoPFR.theorem_3_5_entropic_pfr
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:50.540514+00:00
-- url     : https://prove2.me/theorems/a455120e-e934-4238-b7a3-9ef2af70e7c3
-- title:
--   Theorem 3.5 (entropic PFR, [GGMT25]) — $d[X;U_H]=O(d[X;X])$
-- statement:
--   There is a universal constant $C$ with the following property. For every $n$ and every random variable $X$ on $\mathbb F_2^n$ there is a subspace $H\le\mathbb F_2^n$ with
--   $$d[X;U_H]\le C\,d[X;X].$$
--
--   This is the entropic form of the polynomial Freiman–Ruzsa theorem. The source cites it from Gowers, Green, Manners and Tao and uses it inside the analysis of Claim 5.2.
--
--   Differences from the source:
--
--   - encoding: d[X;U_H] = O(d[X;X]) → ∃ C before n and X, with d[X;U_H] ≤ C · d[X;X]; reason: the O(·) of a universal statement
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 3.5, p.15

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Theorem 3.5 (Entropic PFR, [GGMT25]).** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.15: for every random variable `X` on `F₂ⁿ`
there is a subspace `H ≤ F₂ⁿ` with `d[X;U_H] = O(d[X;X])`.

**Formalization Note.** The `O(·)` constant `C` is universal: it is chosen before `n` and `X`. -/
theorem theorem_3_5_entropic_pfr :
    ∃ C : ℝ, ∀ (n : ℕ) (X : PMF (Vec n)), ∃ H : Submodule (ZMod 2) (Vec n),
      rd X (subspaceLaw H) ≤ C * rd X X := by sorry

end AlgoPFR
