-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_epiConverges_inf_argmin
-- name    : DupacovaWets.Consistency.epiConverges_inf_argmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:47:42.366725+00:00
-- url     : https://prove2.me/theorems/08d09aa9-e9bd-460b-b58d-51432612a281
-- title:
--   Proposition 3.3, p. 14 — epi-convergence: limsup of infima, limits of minimizers, minimum attained in the closure of D
-- statement:
--   Let $g^\nu, g:\mathbb R^n\to[-\infty,\infty]$ with $g=\operatorname{epi-lim}_{\nu\to\infty}g^\nu$. Then:
--
--   1. the optimal values satisfy
--   $$
--   \limsup_{\nu\to\infty}\,(\inf g^\nu)\le\inf g; \tag{3.9}
--   $$
--   2. if $x^k\in\operatorname{argmin} g^{\nu_k}$ along a subsequence $\nu_1<\nu_2<\cdots$ and $x^k\to x$, then $x\in\operatorname{argmin} g$ and $\inf g^{\nu_k}\to\inf g$;
--   3. in particular, if a bounded set $D\subseteq\mathbb R^n$ meets $\operatorname{argmin} g^{\nu_k}$ for every $k$ along some subsequence, then $g$ attains its minimum at a point of the closure of $D$.
--
--   This deterministic proposition (attributed in the paper to Attouch and Wets 1981 and Salinetti and Wets 1986) is the bridge from epi-convergence of objectives to convergence of optimal values and solutions; Theorem 3.9 applies it pathwise.
--
--   **Formalization Note** Functions are `EReal`-valued on `EuclideanSpace ℝ (Fin n)`; a subsequence is a strictly increasing $\varphi:\mathbb N\to\mathbb N$ and the convergence of infima is in the order topology of $[-\infty,\infty]$. The "Moreover" equivalence that follows on p. 14 is not part of this item.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 14, Proposition 3.3, (3.9) through 'closure of D'

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
open Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 14, Proposition 3.3 (through "closure of D"): if
`g = epi-lim g^ν`, then (3.9) `limsup (inf g^ν) ≤ inf g`; if `x^k ∈ argmin g^{ν_k}` along a
subsequence and `x^k → x`, then `x ∈ argmin g` and `inf g^{ν_k} → inf g`; and if a bounded
`D` meets `argmin g^{ν_k}` for every `k` along a subsequence, then `g` attains its minimum at
a point of the closure of `D`. -/
theorem epiConverges_inf_argmin {n : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin n) → EReal)
    (g₀ : EuclideanSpace ℝ (Fin n) → EReal) (hg : EpiConverges g g₀) :
    limsup (fun k => ⨅ x, g k x) atTop ≤ ⨅ x, g₀ x ∧
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ (xs : ℕ → EuclideanSpace ℝ (Fin n))
        (x : EuclideanSpace ℝ (Fin n)), (∀ k, xs k ∈ argminSet (g (φ k))) →
        Tendsto xs atTop (𝓝 x) →
        x ∈ argminSet g₀ ∧ Tendsto (fun k => ⨅ y, g (φ k) y) atTop (𝓝 (⨅ y, g₀ y))) ∧
    (∀ D : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded D → ∀ φ : ℕ → ℕ, StrictMono φ →
        (∀ k, (argminSet (g (φ k)) ∩ D).Nonempty) → ∃ x ∈ closure D, x ∈ argminSet g₀) := by sorry

end DupacovaWets.Consistency
