-- Prove2me | Theorems.Thm_AutoregLTF_eq_11
-- name    : AutoregLTF.eq_11
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:53:19.984202+00:00
-- url     : https://prove2.me/theorems/28cb55c7-a6d7-4721-ab17-32ef1710e5ab
-- title:
--   (11), proof of Lemma 1, p.6 — pointer bits: $f^t_{\theta,i,\mathrm{ptr},j}=\mathbf 1\{t=m+1-j\}$
-- statement:
--   Let $m\ge2$, let $\lambda\in\{0,1\}^{m\times m}$ be a labeling with encoding $\theta$, and fix a row $i\in[m]$. In the recursion (4)–(9),
--
--   $$f^t_{\theta,i,\mathrm{ptr},j}=\mathbf 1\{t=m+1-j\}\qquad(j\in[m+1],\ t\ge0).$$
--
--   The single $1$ among the pointer bits starts at position $m+1$ and moves down one position per round, so at round $t$ it selects digit $m+1-t$; after round $m$ all pointer bits are $0$.
--
--   Differences from the source:
--   - encoding: a labeling λ ∈ {0,1}^{m×m} → lab : ℕ → ℕ → Bool, read only at i, j ∈ [m]; reason: every m×m matrix extends to such a function and the statement reads only the entries in [m]×[m]; same instances
--   - encoding: t = m + 1 − j → (t : ℤ) = m + 1 − j; reason: the equation is read in ℤ to avoid truncated subtraction; for j ≤ m + 1 it is the same equation
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 1, (11), p.6

import Mathlib
import Definitions.Def_AutoregLTF_state

namespace AutoregLTF

/-- **Proof of Lemma 1, (11)**, p.6 (PDF p.6).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

The pointer bits of the recursion (4)–(9) move one step per round:
`f^t_{θ,i,ptr,j} = 1{t = m + 1 − j}` for `j ∈ [m + 1]` and `t ≥ 0`, for every labeling `λ` with
encoding `θ` and every selected row `i ∈ [m]`.

**Formalization Note.** `m ≥ 2` is the standing assumption of §§2–4 (p.4). The labeling is
`lab : ℕ → ℕ → Bool` read at `i, j ∈ [m]`, and `θ = enc m lab`. The equation `t = m + 1 − j` is read
in `ℤ`. -/
theorem eq_11 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (i : ℕ) (hi : i ∈ Finset.Icc 1 m)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (m + 1)) (t : ℕ) :
    (state m (enc m lab) i t).ptr j = decide ((t : ℤ) = (m : ℤ) + 1 - j) := by sorry

end AutoregLTF
