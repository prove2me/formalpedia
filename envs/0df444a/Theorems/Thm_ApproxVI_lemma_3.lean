-- Prove2me | Theorems.Thm_ApproxVI_lemma_3
-- name    : ApproxVI.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:11.452634+00:00
-- url     : https://prove2.me/theorems/7b2a8375-25b9-45a1-8a56-b46a69eb85fb
-- title:
--   Lemma 3 — the interpolation identity $X^n_l(t)=X^n_l(0)+\int_0^tY^n_c+W^n_l(t)+G^n_c(t)$
-- statement:
--   Let $a(n)>0$ with $\sum_n a(n)=\infty$, and let $t_0=0$, $t_n=\sum_{m<n}a(m)$. Let $x_n,\tilde x_n,y_n,M_n,g_n\in\mathbb R^d$ satisfy, for all $n$,
--
--   $$
--   \tilde x_{n+1}=x_n+a(n)\big[y_n+M_{n+1}\big],\qquad g_n=x_{n+1}-\big(x_n+a(n)[y_n+M_{n+1}]\big),
--   $$
--
--   as in the projective scheme (18)–(19). With the trajectories $X_l$, $Y_c$, $W_l$, $G_c$ of §6.1 and their left shifts $X^n_l(t)=X_l(t_n+t)$, $Y^n_c(t)=Y_c(t_n+t)$, $W^n_l(t)=W_l(t_n+t)-W_l(t_n)$, $G^n_c(t)=G_c(t_n+t)-G_c(t_n)$, for every $n$ and every $t\ge0$,
--
--   $$
--   X^n_l(t)=X^n_l(0)+\int_0^tY^n_c(\tau)\,d\tau+W^n_l(t)+G^n_c(t).
--   $$
--
--   The identity writes the shifted interpolated iterates as an integral of the drift plus noise and projection terms, the starting point of the comparison with the differential inclusion.
--
--   Differences from the source:
--   - generalization: x_n the projective iterates of (18) with y_n ∈ H(x_n) and noise satisfying (AV5) → arbitrary sequences x, x̃, y, M, g related by the two displayed equations; reason: the identity is pathwise algebra and uses neither the projection, nor H, nor the noise assumptions; the source's sequences are an instance
--   - generalization: (AV4): a(n) ≥ 0, Σ a(n) = ∞, Σ a(n)² < ∞ → a(n) > 0 and Σ a(n) = ∞ only; reason: Σ a(n)² < ∞ plays no role in the identity
--   - encoding: a(n) ≥ 0 with divisions by a(n) in (20) → a(n) > 0; reason: (20) divides by a(n) and uses the nonempty intervals [t_n, t_{n+1}); only excludes cases where the trajectories are undefined
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Lemma 3, p.22 (objects (18)–(20), pp.21–22)

import Mathlib
import Definitions.Def_ApproxVI_Xl
import Definitions.Def_ApproxVI_Yc
import Definitions.Def_ApproxVI_Gc
import Definitions.Def_ApproxVI_Wl

namespace ApproxVI

open Filter

/-- **Lemma 3**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*,
arXiv:1709.04673v5, p.22: `X^n_l(t) = X^n_l(0) + ∫₀ᵗ Y^n_c(τ) dτ + W^n_l(t) + G^n_c(t)` for
`t ≥ 0`, where (p.22) `X^n_l(t) := X_l(tₙ + t)`, `Y^n_c(t) := Y_c(tₙ + t)`,
`G^n_c(t) := G_c(tₙ + t) − G_c(tₙ)`, `W^n_l(t) := W_l(tₙ + t) − W_l(tₙ)`.

The sequences are those of the projective scheme (18)–(19), p.21:
`x̃ₙ₊₁ = xₙ + a(n)[yₙ + Mₙ₊₁]` and `gₙ = xₙ₊₁ − (xₙ + a(n)[yₙ + Mₙ₊₁])`.

**Formalization Note** The identity is stated for arbitrary sequences `x, y, M` related to
`x̃, g` by these two equations: the projection, the inclusion `yₙ ∈ H(xₙ)` and the noise
assumptions play no role in it. `a(n) > 0` (the divisions by `a(n)` in (20) and the nonempty
intervals `[tₙ, tₙ₊₁)`) and `Σ a(n) = ∞` (every `t ≥ 0` lies in some interval) are the
standing assumptions of §6 that make the trajectories defined on `[0, ∞)`. `∫₀ᵗ` is the
interval integral. -/
theorem lemma_3 {d : ℕ} (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ha_div : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop atTop)
    (x xt y M g : ℕ → Fin d → ℝ)
    (hxt : ∀ n, xt (n + 1) = x n + a n • (y n + M (n + 1)))
    (hg : ∀ n, g n = x (n + 1) - (x n + a n • (y n + M (n + 1))))
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Xl a x xt (tSeq a n + t) =
      Xl a x xt (tSeq a n + 0) + (∫ τ in (0 : ℝ)..t, Yc a y (tSeq a n + τ)) +
        (Wl a M (tSeq a n + t) - Wl a M (tSeq a n)) +
        (Gc a g (tSeq a n + t) - Gc a g (tSeq a n)) := by sorry

end ApproxVI
