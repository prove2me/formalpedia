-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_4_3
-- name    : ArbSlowFP.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:55.861112+00:00
-- url     : https://prove2.me/theorems/65590470-34c5-4e21-8a01-44687f67e5bb
-- title:
--   Lemma 4.3 — phase length and height of a clock and a parent bundle, (17), (18)
-- statement:
--   For an order-$k$ clock put $L_k=(\mathbf 1_m^\top C)_{k-1}/(k-1)!$ and $h_k=\chi_{k-1}/(k-1)!$. Then $L_k,h_k>0$, and as $q\to\infty$,
--   $$|W_k(q)|=L_kq^{k-1}+O(q^{k-2}),\qquad \chi(q)=h_kq^{k-1}+O(q^{k-2}).$$
--   For a fixed positive integer $\tau$,
--   $$\sum_{\sigma=\tau q}^{2\tau q-1}|W_k(\sigma)|=\frac{L_k\tau^k(2^k-1)}kq^k+O(q^{k-1}).$$
--   If a polynomial $\zeta$ satisfies $\zeta(q)-\zeta(q-1)=\chi(2\tau q)-\chi(\tau q)+c$ for a fixed constant $c\in\mathbb R$, then
--   $$\zeta(q)=\frac{h_k\tau^{k-1}(2^{k-1}-1)}kq^k+O(q^{k-1}).$$
--
--   This explains the exponent before any coupling is chosen.
--
--   **Formalization Note** The asymptotics are along natural $q$. The difference equation is assumed at integers $q\ge1$, which determines the polynomial identity.
--
--   Differences from the source:
--   - encoding: the difference equation for the polynomial ζ, at unspecified q → assumed at all integers q ≥ 1; reason: a polynomial identity is determined by infinitely many points; this form assumes the least
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.27, Lemma 4.3

import Mathlib
import Definitions.Def_ArbSlowFP_IsClock

open Matrix Asymptotics Filter

namespace ArbSlowFP

/-- Lemma 4.3, p.27 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). For an order-k
clock, with `L_k = (1⊤C)_{k-1}/(k-1)! > 0` and `h_k = χ_{k-1}/(k-1)! > 0`: `|W_k(q)| = L_k q^{k-1} + O(q^{k-2})`,
`χ(q) = h_k q^{k-1} + O(q^{k-2})`, (17) the parent bundle length for each fixed `τ ≥ 1`, and (18) for every
polynomial `ζ` with `ζ(q) - ζ(q-1) = χ(2τq) - χ(τq) + c`.

**Formalization Note.** `O` is as `q → ∞` along `ℕ`. The bundle sum runs over `σ = τq, …, 2τq-1`.
The difference equation for `ζ` is assumed at all integers `q ≥ 1`, which determines the
polynomial identity. -/
theorem lemma_4_3 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (Lk hk : ℝ)
    (hLk : Lk = (lastCoef ((1 : ι → ℚ) ᵥ* d.C) : ℝ) / ((k - 1).factorial : ℝ))
    (hhk : hk = (lastCoef (d.R d.b) : ℝ) / ((k - 1).factorial : ℝ)) :
    0 < Lk ∧ 0 < hk ∧
    (fun q : ℕ => ((d.W q).length : ℝ) - Lk * (q : ℝ) ^ (k - 1)) =O[atTop]
      (fun q : ℕ => (q : ℝ) ^ (k - 2)) ∧
    (fun q : ℕ => ((d.chiAt q : ℚ) : ℝ) - hk * (q : ℝ) ^ (k - 1)) =O[atTop]
      (fun q : ℕ => (q : ℝ) ^ (k - 2)) ∧
    ∀ τ : ℕ, 1 ≤ τ →
      (fun q : ℕ => (∑ σ ∈ Finset.Ico (τ * q) (2 * τ * q), ((d.W σ).length : ℝ)) -
          Lk * (τ : ℝ) ^ k * (2 ^ k - 1) / (k : ℝ) * (q : ℝ) ^ k) =O[atTop]
        (fun q : ℕ => (q : ℝ) ^ (k - 1)) ∧
      ∀ (ζ : Polynomial ℝ) (c : ℝ),
        (∀ q : ℕ, 1 ≤ q → ζ.eval (q : ℝ) - ζ.eval ((q : ℝ) - 1) =
          ((d.chiAt (2 * τ * q) : ℚ) : ℝ) - ((d.chiAt (τ * q) : ℚ) : ℝ) + c) →
        (fun q : ℕ => ζ.eval (q : ℝ) -
            hk * (τ : ℝ) ^ (k - 1) * (2 ^ (k - 1) - 1) / (k : ℝ) * (q : ℝ) ^ k) =O[atTop]
          (fun q : ℕ => (q : ℝ) ^ (k - 1)) := by sorry

end ArbSlowFP
