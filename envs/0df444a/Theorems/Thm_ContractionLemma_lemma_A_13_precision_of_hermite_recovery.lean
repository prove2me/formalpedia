-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_13_precision_of_hermite_recovery
-- name    : ContractionLemma.lemma_A_13_precision_of_hermite_recovery
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:56.71758+00:00
-- url     : https://prove2.me/theorems/507d6c77-4f5a-4e6d-8088-870ace3ea755
-- title:
--   Lemma A.13 — precision of Hermite recovery
-- statement:
--   Let $q_0\ge q_1\ge\dots\ge 0$, put $m_t=q_{v_2(t)}$ for $t\in\mathcal E$, and suppose $\sum_{t\in\mathcal E}m_t>\deg F$. Let $E_t$ be as in (7), and let $R_t(z)$ be the polynomial formed by the terms of degree below $m_t$ of the power series $F(t+\alpha z)/E_t(t+\alpha z)$. Then:
--
--   1. (recovery) $F(0)=\sum_{t\in\mathcal E}E_t(0)R_t(-t/\alpha)$;
--   2. (division is free) for every $t\in\mathcal E$, the power series $1/E_t(t+\alpha z)$ has constant term $1$, and all its coefficients are rationals with odd denominators;
--   3. (the loss) for every $t\in\mathcal E$ of level $i$,
--   $$
--   -v_2(E_t(0))=D_i\sum_{j=1}^{a-i}\frac{j}{2^j}\,(q_i-q_{i+j})\ \ge\ 0;
--   $$
--   4. (precision needed) if for every $t\in\mathcal E$ the first $m_t$ coefficients of $F(t+\alpha z)$ are known modulo $2^{p_t}$, where $p_t\ge p-v_2(E_t(0))+m_t(a+1)$, then $F(0)$ is known modulo $2^p$.
--
--   This measures how many bits the recovery loses: only the drops between levels cost precision.
--
--   **Formalization Note** "Known modulo" reads: for any values congruent to the coefficients modulo $2^{p_t}$, the recovery formula computed from those values is congruent to $F(0)$ modulo $2^p$.
--
--   Differences from the source:
--   - reading: the first m_t coefficients are known modulo 2^{p_t}; then F(0) is known modulo 2^p → for all data y congruent to the coefficients, the recovery formula built from y is congruent to F(0) modulo 2^p; reason: this is the operational meaning of "known", as in the proof
--   - generalization: F the rewiring polynomial with integer tables → any F over ℚ; reason: the proof of the congruence uses only the exact identity (a) for the difference; the rewiring polynomial is a special case
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.13, p.71; proof pp.92–93

import Mathlib
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_zoom
import Definitions.Def_ContractionLemma_Et

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.13 (Precision of Hermite recovery)** — Gajulapalli, *The Contraction Lemma Beyond
ETH* (manuscript, sha256 049caea1…), p.71 (PDF p.74); proof pp.92–93.

Let `q_0 ≥ q_1 ≥ ⋯ ≥ 0`, put `m_t = q_{v₂(t)}` for `t ∈ E`, and suppose `∑_{t∈E} m_t > deg F`.
Let `E_t` be as in (7), and let `R_t(z)` be the terms of degree below `m_t` of
`F(t + αz)/E_t(t + αz)`.
(a) (recovery) `F(0) = ∑_{t∈E} E_t(0) R_t(−t/α)`.
(b) (division is free) `1/E_t(t + αz)` has constant term `1` and coefficients with odd
denominators.
(c) (the loss) for `t` of level `i`, `−v₂(E_t(0)) = D_i ∑_{j=1}^{a−i} (j/2^j)(q_i − q_{i+j}) ≥ 0`,
with `D_i = L/2^i`.
(d) (precision needed) if, for every `t ∈ E`, the first `m_t` coefficients of `F(t + αz)` are
known modulo `2^{p_t}` with `p_t ≥ p − v₂(E_t(0)) + m_t(a + 1)`, then `F(0)` is known modulo
`2^p`.

**Formalization Note.** `F` is any polynomial over `ℚ` (the paper applies the lemma to the
rewiring polynomial). (d) reads "known modulo `2^{p_t}`" as: for any values `y_{t,k}` congruent
to the coefficients modulo `2^{p_t}`, the recovery formula of (a) computed from the `y_{t,k}`
(`RtOfData`) is congruent to `F(0)` modulo `2^p`. -/
theorem lemma_A_13_precision_of_hermite_recovery (a : ℕ) (q : ℕ → ℕ) (hq : Antitone q)
    (F : ℚ[X]) (hdeg : F.degree < ((∑ t ∈ easyPts a, orderAt q t : ℕ) : WithBot ℕ)) :
    F.eval 0 = ∑ t ∈ easyPts a, (Et a q t).eval 0 * (Rt a q t F).eval (-(t : ℚ) / alpha a) ∧
    (∀ t ∈ easyPts a, PowerSeries.constantCoeff (invZoomEt a q t) = 1 ∧
      ∀ k, ¬ 2 ∣ (PowerSeries.coeff k (invZoomEt a q t)).den) ∧
    (∀ t ∈ easyPts a,
      -((padicValRat 2 ((Et a q t).eval 0) : ℤ) : ℚ) =
          (2 : ℚ) ^ (a - padicValInt 2 t) * ∑ j ∈ Finset.Icc 1 (a - padicValInt 2 t),
            ((j : ℚ) / 2 ^ j) * ((q (padicValInt 2 t) : ℚ) - q (padicValInt 2 t + j)) ∧
        0 ≤ -((padicValRat 2 ((Et a q t).eval 0) : ℤ) : ℚ)) ∧
    (∀ (p : ℤ) (pt : ℤ → ℤ) (y : ℤ → ℕ → ℚ),
      (∀ t ∈ easyPts a,
        p - padicValRat 2 ((Et a q t).eval 0) + (orderAt q t : ℤ) * ((a : ℤ) + 1) ≤ pt t) →
      (∀ t ∈ easyPts a, ∀ k < orderAt q t, ratCongr (pt t) (y t k) ((zoom a t F).coeff k)) →
      ratCongr p (F.eval 0)
        (∑ t ∈ easyPts a, (Et a q t).eval 0 * (RtOfData a q t (y t)).eval (-(t : ℚ) / alpha a))) := by sorry

end ContractionLemma
