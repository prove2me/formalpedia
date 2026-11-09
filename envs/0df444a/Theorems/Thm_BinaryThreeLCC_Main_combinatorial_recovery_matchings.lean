-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_combinatorial_recovery_matchings
-- name    : BinaryThreeLCC.Main.combinatorial_recovery_matchings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:38.373195+00:00
-- url     : https://prove2.me/theorems/19929d6c-3fa9-43c0-b05f-916a530d4f10
-- title:
--   Fact 2.1 — combinatorial recovery matchings (corrected: integer corruption radius)
-- statement:
--   Let $C:\mathbb F_2^k\to\mathbb F_2^n$, $n\ge1$, be an injective linear $(3,\delta,\varepsilon)$-locally correctable code, where $0<\delta<1$ and $0\le\varepsilon<1/2$. Let $v_u$ be row $u$ of its encoding matrix for the first $n$ positions, and put $v_u=0$ at the remaining $n$ positions. The padded rows have span dimension $k$. There exist matchings $\mathcal H_u$ for every $u\in[2n]$ such that
--
--   $$\mathcal H_u\subseteq\binom{[2n]\setminus\{u\}}3,\qquad
--   |\mathcal H_u|\ge\frac{\lfloor\delta n\rfloor}{3},\qquad
--   v_u=\sum_{a\in e}v_a\quad(e\in\mathcal H_u).$$
--
--   Distinct hyperedges within each matching are disjoint. This supplies the combinatorial recovery equations from the operational corrector, preserving the doubled length and full rank.
--
--   Differences from the source:
--   - correction: |H_u| ≥ δn/3 → |H_u| ≥ floor(δn)/3; reason: n=k=1, the identity encoding, δ=1/4 and ε=0 have an exact one-query corrector, but the doubled two-element vertex set has no triple excluding u
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Fact 2.1, printed p. 2, PDF p. 4; statement continues on printed p.3, PDF p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Matchings

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Fact 2.1, corrected only for the integer corruption budget. -/
theorem combinatorial_recovery_matchings {k n : ℕ} (hn : 0 < n)
    (C : CodeModel k n) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 ≤ ε) (hε1 : ε < 1 / 2) (hcorrect : Corrects C δ ε) :
    spanDimension (paddedRow C) = k ∧
    ∃ H : Fin (2 * n) → Finset (Finset (Fin (2 * n))),
      (∀ u, IsRecoveryMatching u (H u)) ∧
      (∀ u, ((⌊δ * (n : ℝ)⌋₊ : ℕ) : ℝ) / 3 ≤ ((H u).card : ℝ)) ∧
      ∀ u, ∀ e ∈ H u, paddedRow C u = ∑ a ∈ e, paddedRow C a := by sorry

end BinaryThreeLCC.Main
