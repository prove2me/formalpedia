-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_lemma_4_1
-- name    : ConservativePJ.ManyPlayers.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:44.230204+00:00
-- url     : https://prove2.me/theorems/a34a9df2-0725-4ec6-978a-edc1bddf9841
-- title:
--   Lemma 4.1 — adding a player raises the success probability from $p$ to $p+\gamma(p)$
-- statement:
--   **Adding a player.** Let $n\ge2$, $m\ge2$, $1\le w\le n$, $0<p<1$, $d=\lceil n/w\rceil$, and fix a partition of $[n]$ into $w$ parts $G_1,\dots,G_w$ of size at most $d$. Let $P$ be a public-coin conservative protocol for $\widehat{\mathrm{MPJ}}_m$ (resp. $\mathrm{MPJ}_m$) with alphabets $M_1,\dots,M_{m-1}$ that succeeds with probability at least $p$ on every input, whose first message has at most $w$ bits and whose other messages before the output have at most $w+1$ bits each. Then there is a public-coin conservative protocol $P^+$ for $\widehat{\mathrm{MPJ}}_{m+1}$ (resp. $\mathrm{MPJ}_{m+1}$) that succeeds with probability at least
--   $$p+\gamma(p),\qquad \gamma(p)=\frac{\min\{p,1-p\}}{32\sqrt{1+dp}},$$
--   on every input, and whose alphabets are: $2^w$ values for the first message (one sign for each part, $w$ bits), $2|M_1|$ values for the second (one bit followed by a first message of $P$), and $M_{i-1}$ for Player $i$, $3\le i\le m$.
--
--   Iterating the lemma is how the randomized protocols of Section 4 are built (Lemma 4.2).
--
--   Differences from the source:
--   - encoding: "The same holds with MPJ in place of MPĴ" (a separate sentence) → one statement quantified over `pb : Problem` (`.hat` = MPĴ, `.bool` = MPJ); reason: both cases at once; same content
--   - encoding: §4 standing assumption "we assume that n ≥ 2" (p. 9), not repeated in the lemma → hypothesis `2 ≤ n`; reason: the section's standing assumption made explicit
--   - encoding: a partition of [n] into w parts of size at most d → `G : Fin n → Fin w` surjective, every fibre of size ≤ d (`IsPartition G d`); reason: the parts are the fibres; same partitions
--   - encoding: d = ⌈n/w⌉ → `partBound n w = ⌈(n : ℝ)/w⌉₊`; reason: same number
--   - encoding: "first message has at most w bits, other messages before the output at most w + 1 bits each" → `LengthShape M w`: ℓ_1 ≤ w and ℓ_i ≤ w + 1 for 2 ≤ i ≤ m − 1; reason: same condition
--   - reading: "The first message of P+ consists of one sign for each part … Its second message consists of one bit followed by the first message of P, and for 3 ≤ i ≤ m, Player i of P+ sends a message of Player i − 1 of P" → P+ has exactly the alphabets `addPlayerAlphabet w M` = (2^w, 2|M_1|, |M_2|, …, |M_{m−1}|); reason: the clauses describe the message sets of P+ (how the lemma is iterated in Lemma 4.2 and A.3.9); all their lengths are kept exactly
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 10 (PDF 12), Lemma 4.1; proof App. A.3.1, pp. 19–21 (PDF 21–23)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem lemma_4_1 (pb : Problem) (n m w : ℕ) (p : ℝ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hw1 : 1 ≤ w) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (G : Fin n → Fin w) (hG : IsPartition G (partBound n w))
    (M : Fin (m - 1) → ℕ) (P : RandProtocol n m pb M)
    (hP : ∀ x, p ≤ P.successProb x) (hshape : LengthShape M w) :
    ∃ P' : RandProtocol n (m + 1) pb (addPlayerAlphabet w M),
      ∀ x, p + gain (partBound n w) p ≤ P'.successProb x := by sorry

end ConservativePJ.ManyPlayers
