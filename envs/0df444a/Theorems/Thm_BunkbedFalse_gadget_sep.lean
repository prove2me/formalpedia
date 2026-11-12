-- Prove2me | Theorems.Thm_BunkbedFalse_gadget_sep
-- name    : BunkbedFalse.gadget_sep
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:29:46.403239+00:00
-- url     : https://prove2.me/theorems/79bb03d2-e0eb-4b5d-80b2-cb1b8fda1379
-- title:
--   Lemma 5.3 — $\mathbb{P}_P(a \nleftrightarrow v_1 \leftrightarrow v_n) = P^{2n-1}$
-- statement:
--   In the gadget graph $G_n$, for $n \ge 3$ and $0 < P < 1$,
--
--   $$\mathbb{P}_P\bigl(a \nleftrightarrow v_1 \leftrightarrow v_n\bigr) \;=\; P^{2n-1}.$$
--
--   In words: the probability that $v_1$ and $v_n$ lie in a common component which does **not** contain $a$. Such a component must contain the whole path $v_1 \to v_2 \to \dots \to v_n$, which requires its $n-1$ edges to be open, and every one of the $n$ spokes at $a$ must be closed; these events have probabilities $P^{n-1}$ and $P^{n}$ respectively.
--
--   **Formalization Note** This is the partition probability $P_{a|bc}$ for $a = 0$, $b = v_1$, $c = v_n$. Note $2n - 1$ is natural-number subtraction, which is harmless since $n \ge 3$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 8, Lemma 5.3.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Lemma 5.3** (p. 8). `ℙ_P(a ↮ v₁ ↔ vₙ) = P^{2n-1}`. -/
theorem gadget_sep (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = P ^ (2 * n - 1) := by sorry

end BunkbedFalse
