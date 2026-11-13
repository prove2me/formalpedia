-- Prove2me | Theorems.Thm_AutoregLTF_lemma_2
-- name    : AutoregLTF.lemma_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:39.275308+00:00
-- url     : https://prove2.me/theorems/78661eb2-d1a0-4d0c-92ee-13defa17fa73
-- title:
--   Lemma 2, p.8 — one LTF of window $p+1$ maps each block $E^t_{\theta,i}$ to $E^{t+1}_{\theta,i}$
-- statement:
--   Let $m\ge2$ and $p=378(m+2)$. For every $\theta\in\{0,\dots,2^m-1\}^m$ there are integers $B>0$ and $a_1,\dots,a_{p+1}$ such that, for every $i\in[m]$ and $t\ge0$, the recurrence
--
--   $$z_n=\mathbf 1\Big\{-B+\sum_{\ell=1}^{p+1}a_\ell z_{n-\ell}\ge0\Big\}\qquad(16)$$
--
--   started from the history $z_{-p-1}=0$, $z_{-p+r}=E^t_{\theta,i,r}$ ($0\le r<p$) generates $z_r=E^{t+1}_{\theta,i,r}$ for $0\le r<p$.
--
--   $B$ and the $a_\ell$ depend only on $m$ and $\theta$, not on the row $i$ or the round $t$: a single LTF performs every round of the recursion (4)–(9) for every row.
--
--   Differences from the source:
--   - encoding: integers a_1, …, a_{p+1} → a : ℕ → ℤ, of which (16) reads a_1, …, a_{p+1}; reason: the other values are never read; same instances
--   - encoding: θ ∈ {0, …, 2^m − 1}^m → θ : ℕ → ℤ with 0 ≤ θ j ≤ 2^m − 1 for j ∈ [m]; reason: only θ_1, …, θ_m are read and every vector in the range extends to such a function; same instances
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Lemma 2, p.8

import Mathlib
import Definitions.Def_AutoregLTF_gen16

namespace AutoregLTF

/-- **Lemma 2**, p.8 (PDF p.8).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"For every `θ ∈ {0, …, 2^m − 1}^m`, there are integers `B > 0` and `a_1, …, a_{p+1}` such that, for
every `i ∈ [m]` and `t ≥ 0`, the history `(0, E^t_{θ,i})` generates `E^{t+1}_{θ,i}` as its next `p` bits
under (16)."

**Formalization Note.** `m ≥ 2` is the standing assumption of §§2–4 (p.4). The coefficients are
`a : ℕ → ℤ`, of which (16) reads `a_1, …, a_{p+1}`. `gen16 (p m) B a (hist m θ i t)` is the run of (16)
from the history `(0, E^t_{θ,i})`, and its position `p + 1 + r` is `z_r`, the `r`-th generated bit. `B`
and `a` are chosen before `i` and `t` ("the coefficients depend only on `m` and `θ`", p.11). -/
theorem lemma_2 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) :
    ∃ B : ℤ, 0 < B ∧ ∃ a : ℕ → ℤ, ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m θ i t) (p m + 1 + r) = E m θ i (t + 1) r := by sorry

end AutoregLTF
