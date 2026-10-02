-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_sherali_adams_reaches_hull
-- name    : Disjunctive.HigherDim.sherali_adams_reaches_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:42:23.990125+00:00
-- url     : https://prove2.me/theorems/f3c0bd6d-47e7-4c74-a62c-31a72ec67afc
-- title:
--   Theorem 7.6 — the Sherali-Adams hierarchy reaches the integer hull
-- statement:
--   This is Theorem 7.6 of Balas's *Disjunctive Programming*, the goal theorem of this
--   mission, cited to Sherali and Adams [112]:
--
--   $$
--   K_p = \mathrm{conv}(K_0).
--   $$
--
--   **Correcting `BRIEF.md`.** The brief's "Recommended goal theorem" section mislabels this result
--   as "the Lovász-Schrijver $N$-operator reaches the integer hull: $K^p = \mathrm{conv}(K_0)$" — but
--   the source text (p. 95, PDF 101) states Theorem 7.6 as `[112] Kp = conv(K0)`, immediately after
--   introducing $K_t$ in the *Sherali-Adams* construction of Section 7.3, and cites Sherali-Adams
--   explicitly. The actual Lovász-Schrijver iteration-reaches-hull result is Theorem 7.5 (`Np(K) =
--   conv(K0)`, cited `[99]`), formalized separately above as
--   `lovasz_schrijver_reaches_hull`. See `STATUS.md` for this correction.
--
--   The book gives two independent proofs, both from results already in this mission: "Now Theorem
--   7.6 follows from Corollary 7.3 and Theorem 7.7" ($K_p \subseteq P_{1,\dots,p}(K) =
--   \mathrm{conv}(K_0)$ by Theorem 7.7 at $t=p$ and Corollary 7.3, combined with the easy
--   $K_0 \subseteq K_p$ direction) — the proof path formalized here — and, alternatively, "from
--   Theorem 7.5 and a proposition in [99] that shows $K_t \subseteq N^t(K)$" (not formalized: the
--   `[99]` proposition is an external citation with no page reference in this chapter).
--
--   **Formalization Note.** Stated with the two hypotheses the book's chosen proof path needs:
--   `Convex ℝ (KtSet A b N' p)` (so that `conv(K0) ⊆ Kp` follows from `K0Set ⊆ KtSet ... p`, "It is easy
--   to see that $K_0 \subseteq K_p$", together with $K_p$ already being convex) and `K0Set A b N' ⊆
--   KtSet A b N' p` (the chain $K_0 \subseteq K_p \subseteq \cdots \subseteq K_1 \subseteq K$ the
--   book asserts "It is easy to see"). The reverse inclusion $K_p \subseteq \mathrm{conv}(K_0)$ is
--   exactly `sherali_adams_subset_iterated_split` at $S = N'$, $t = |N'| = p$, combined with
--   `full_split_convexification`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 95, Theorem 7.6

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts

namespace Disjunctive.HigherDim

/-- Theorem 7.6 (Balas §7.3, p. 96, [112]): the Sherali-Adams hierarchy reaches the convex hull
of `K₀` at its top level `t = |N'|`. Convexity of `K_t` and `K₀ ⊆ K_t` are half of that
conclusion (with Theorem 7.7 they give it), so they are proved, not assumed. -/
theorem sherali_adams_reaches_hull {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) :
    KtSet A b Nprime Nprime.card = convexHull ℝ (K0Set A b Nprime) := by sorry

end Disjunctive.HigherDim
