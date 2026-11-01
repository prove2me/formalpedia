-- Prove2me | Theorems.Thm_ActiveCtxSearch_eq_28_phi
-- name    : ActiveCtxSearch.eq_28_phi
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:29.908085+00:00
-- url     : https://prove2.me/theorems/0f934e7d-6e0b-4745-b89c-90bac12269c7
-- title:
--   Eq. (28) (corrected: scaling by $1/\|w^*\|_2$) — the link $\varphi$ and its properties
-- statement:
--   Assume (A1)–(A3), and let $\varphi(\Delta)=F_\xi(0)-F_\xi(-\Delta)$ with $F_\xi$ the distribution function of the noise. Then:
--
--   1. $\eta_b(x)-\tfrac12=\varphi(v(x)-b)$ for every context $x$ and action $b$, where $\eta_b(x)=\Pr[y=1\mid x,b]$;
--   2. $\varphi(\Delta)\le0$ for $\Delta\le0$, $\varphi(\Delta)\ge0$ for $\Delta\ge0$, and $\varphi(0)=0$;
--   3. for $-2\le s\le t\le 2$,
--   $$\frac{c_\xi}{\|w^*\|_2}(t-s)\le\varphi(t)-\varphi(s);$$
--   4. for all $s\le t$,
--   $$\varphi(t)-\varphi(s)\le\frac{C_\xi}{\|w^*\|_2}(t-s).$$
--
--   These are the properties of the link between the margin $v(x)-b$ and the label probability used in Lemmas 1 and 4–6.
--
--   Differences from the source:
--   - correction: φ′(Δ) = f_ξ(−Δ) ∈ [c_ξ, C_ξ] for |Δ| ≤ 2 → increments between (c_ξ/‖w*‖₂)(t − s) and (C_ξ/‖w*‖₂)(t − s); reason: (A3) bounds f_ξ by c_ξ/‖w*‖₂ and C_ξ/‖w*‖₂, not by c_ξ, C_ξ: ‖w*‖₂ = 1/2, ξ ∼ Unif[−2, 2], c_ξ = C_ξ = 1/8 satisfy (A3) and f_ξ = 1/4 ∉ [1/8, 1/8]
--   - encoding: a bound on the derivative φ′ → bounds on the increments φ(t) − φ(s); reason: f_ξ is only a density, so φ′ = f_ξ(−·) holds almost everywhere; the increment form is what the proofs integrate
--   - reading: Δ_b(x) := v(x) − b = ⟨x, w*⟩ + μ* − b (27) → Δ_b(x) = v(x) − b = ⟨x, w*⟩ − μ* − b; reason: the expansion contradicts v(x) = ⟨x, w*⟩ − μ* of (1); a sign slip
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Appendix A, Eqs. (27)–(28) and the sentence after (28), p.28

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors

open MeasureTheory

namespace ActiveCtxSearch

/-- **Eq. (28) and the properties of `φ`** (corrected: scaling by `1/‖w*‖₂`), Chen, Liu & Wang,
arXiv:2110.01072v2, p.28. Under (A1)–(A3):

1. `η_b(x) − 1/2 = φ(v(x) − b)` for every context `x` and action `b`;
2. `φ(Δ) ≤ 0` for `Δ ≤ 0`, `φ(Δ) ≥ 0` for `Δ ≥ 0`, and `φ(0) = 0`;
3. `(c_ξ/‖w*‖₂)(t − s) ≤ φ(t) − φ(s)` for `−2 ≤ s ≤ t ≤ 2`;
4. `φ(t) − φ(s) ≤ (C_ξ/‖w*‖₂)(t − s)` for all `s ≤ t`.

**Formalization Note** The source writes `φ′(Δ) = f_ξ(−Δ) ∈ [c_ξ, C_ξ]` for `|Δ| ≤ 2`; (A3) bounds
`f_ξ` by `c_ξ/‖w*‖₂` and `C_ξ/‖w*‖₂` (counterexample to the unscaled form: `‖w*‖₂ = 1/2`,
`ξ ∼ Unif[−2, 2]`, `c_ξ = C_ξ = 1/8`). `f_ξ` is a density, so `φ′ = f_ξ(−·)` holds only almost everywhere;
the derivative bounds are stated as increment bounds. The source's (27) expands
`Δ_b(x) = v(x) − b` as `⟨x, w*⟩ + μ* − b`, a sign slip; `v(x) − b = ⟨x, w*⟩ − μ* − b` is used. -/
theorem eq_28_phi (θ : Params) {d : ℕ} (I : Problem d) (hA : Assumptions θ I) :
    (∀ (x : E d) (b : ℝ), I.eta b x - 1 / 2 = I.phi (I.v x - b)) ∧
      (∀ Δ : ℝ, Δ ≤ 0 → I.phi Δ ≤ 0) ∧ (∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ I.phi Δ) ∧ I.phi 0 = 0 ∧
      (∀ s t : ℝ, -2 ≤ s → s ≤ t → t ≤ 2 → θ.cξ / ‖I.w‖ * (t - s) ≤ I.phi t - I.phi s) ∧
      (∀ s t : ℝ, s ≤ t → I.phi t - I.phi s ≤ θ.Cξ / ‖I.w‖ * (t - s)) := by sorry

end ActiveCtxSearch
