-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_lemma_A_3_2
-- name    : ConservativePJ.ManyPlayers.lemma_A_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:53.802711+00:00
-- url     : https://prove2.me/theorems/c5694998-616d-4a44-b00a-84e8bd68ecbe
-- title:
--   Lemma A.3.2 — fixing the random strings: $r=\lceil b/w\rceil$ players in front give a deterministic protocol correct on every input
-- statement:
--   **Fixing the random strings.** Let $n\ge2$, $m\ge2$, $1\le w\le n$, $d=\lceil n/w\rceil$, and fix a partition of $[n]$ into $w$ parts of size at most $d$. Let $P$ be a public-coin conservative protocol for $\widehat{\mathrm{MPJ}}_m$ (resp. $\mathrm{MPJ}_m$), with alphabets $M_1,\dots,M_{m-1}$, whose error probability is at most $1/(2d)$ on every input. Put
--   $$L=\big\lceil 2^w\,(nm\ln n+1)\big\rceil,\qquad b=\lceil\log L\rceil,\qquad r=\lceil b/w\rceil .$$
--   Then there is a deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_{m+r}$ (resp. $\mathrm{MPJ}_{m+r}$) that is correct on every input, in which Players $1,\dots,r$ send at most $w$ bits each and $b$ bits in all, Player $r+1$ sends $\lceil\log w\rceil$ bits followed by a first message of $P$ (alphabet of size $2^{\lceil\log w\rceil}|M_1|$), and Player $r+i$ sends a message of Player $i$ of $P$ (alphabet $M_i$) for $2\le i\le m-1$.
--
--   Together with Lemma A.3.9 it turns the randomized protocols into the deterministic ones of Theorem 4.4.
--
--   Differences from the source:
--   - encoding: "The same holds with MPJ in place of MPĴ" (a separate sentence) → one statement quantified over `pb : Problem` (`.hat` = MPĴ, `.bool` = MPJ); reason: both cases at once; same content
--   - encoding: §4 standing assumption "we assume that n ≥ 2" (p. 9), not repeated in the lemma → hypothesis `2 ≤ n`; reason: the section's standing assumption made explicit
--   - encoding: a partition of [n] into w parts of size at most d → `G : Fin n → Fin w` surjective, every fibre of size ≤ d (`IsPartition G d`); reason: the parts are the fibres; same partitions
--   - encoding: d = ⌈n/w⌉ → `partBound n w = ⌈(n : ℝ)/w⌉₊`; reason: same number
--   - encoding: log (base two) and ln → `Real.logb 2` and `Real.log`; reason: the paper's convention (§2): logarithms are to base two, ln is natural
--   - reading: "Players 1, …, r send at most w bits each and b bits in all. Player r + 1 sends ⌈log w⌉ bits followed by a first message of P, and … Player r + i sends a message of Player i of P" → ℓ_i ≤ w for i ≤ r and ℓ_1 + ⋯ + ℓ_r = b; the alphabet of Player r + 1 has 2^⌈log w⌉·|M_1| values and that of Player r + i is M_i; reason: the clauses describe the message sets; all their lengths are kept exactly
--   - encoding: L = ⌈2^w(nm ln n + 1)⌉, b = ⌈log L⌉, r = ⌈b/w⌉ → `L = ⌈2^w (n · m · Real.log n + 1)⌉₊`, `b = Nat.clog 2 L`, `r = ⌈b/w⌉₊`; reason: same numbers (L ≥ 1)
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 22 (PDF 24), Lemma A.3.2 (App. A.3.1); proof p. 22 (PDF 24)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem lemma_A_3_2 (pb : Problem) (n m w : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hw1 : 1 ≤ w) (hwn : w ≤ n) (G : Fin n → Fin w) (hG : IsPartition G (partBound n w))
    (M : Fin (m - 1) → ℕ) (P : RandProtocol n m pb M)
    (hP : ∀ x, P.errorProb x ≤ 1 / (2 * (partBound n w : ℝ))) :
    let L : ℕ := ⌈(2 : ℝ) ^ w * ((n : ℝ) * (m : ℝ) * Real.log n + 1)⌉₊
    let b : ℕ := Nat.clog 2 L
    let r : ℕ := ⌈(b : ℝ) / (w : ℝ)⌉₊
    ∃ (M' : Fin (m + r - 1) → ℕ) (P' : DetProtocol n (m + r) pb M'),
      (∀ x, P'.Correct x) ∧
      (∀ i : Fin (m + r - 1), i.val < r → msgLength (M' i) ≤ w) ∧
      (∑ i : Fin (m + r - 1), (if i.val < r then msgLength (M' i) else 0)) = b ∧
      (∀ i : Fin (m + r - 1), i.val = r → M' i = 2 ^ Nat.clog 2 w * M ⟨0, by omega⟩) ∧
      (∀ i : Fin (m + r - 1), r < i.val →
        M' i = M ⟨i.val - r, by have := i.isLt; omega⟩) := by sorry

end ConservativePJ.ManyPlayers
