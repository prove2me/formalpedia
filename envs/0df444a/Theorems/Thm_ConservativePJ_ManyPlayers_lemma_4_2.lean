-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_lemma_4_2
-- name    : ConservativePJ.ManyPlayers.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:48.647431+00:00
-- url     : https://prove2.me/theorems/934d424a-a81f-496d-b70f-4538d31cc850
-- title:
--   Lemma 4.2 — number of steps: $u\ge U$ added players give an ε-error protocol with total communication $\le T_0+u(w+1)$
-- statement:
--   **Number of steps.** Let $n\ge2$, $m\ge2$, $1\le w\le n$, $0<p_0<1$, $0<\varepsilon<1$, $d=\lceil n/w\rceil$, and
--   $$U=\begin{cases}3+47\ln\!\big(1/(dp_0)\big)+65\sqrt d\,\log(2/\varepsilon)&\text{if }dp_0\le1,\\ 2+65\sqrt d\,\log(2/\varepsilon)&\text{if }dp_0>1,\end{cases}$$
--   with $\log=\log_2$. Let $P_0$ be a public-coin conservative protocol for $\widehat{\mathrm{MPJ}}_m$ (resp. $\mathrm{MPJ}_m$) that succeeds with probability at least $p_0$ on every input, whose first message has at most $w$ bits, whose other messages before the output have at most $w+1$ bits each, and whose total communication is $T_0$. Then for every integer $u\ge U$ there is an $\varepsilon$-error public-coin conservative protocol for $\widehat{\mathrm{MPJ}}_{m+u}$ (resp. $\mathrm{MPJ}_{m+u}$) whose first message has at most $w$ bits, whose other messages before the output have at most $w+1$ bits each, and whose total communication is at most $T_0+u(w+1)$.
--
--   This gives the randomized upper bounds of Section 4 from a uniform guess or from the protocol of Damm, Jukna and Sgall.
--
--   Differences from the source:
--   - encoding: "The same holds with MPJ in place of MPĴ" (a separate sentence) → one statement quantified over `pb : Problem` (`.hat` = MPĴ, `.bool` = MPJ); reason: both cases at once; same content
--   - encoding: §4 standing assumption "we assume that n ≥ 2" (p. 9), not repeated in the lemma → hypothesis `2 ≤ n`; reason: the section's standing assumption made explicit
--   - encoding: d = ⌈n/w⌉ → `partBound n w = ⌈(n : ℝ)/w⌉₊`; reason: same number
--   - encoding: "first message has at most w bits, other messages before the output at most w + 1 bits each" → `LengthShape M w`: ℓ_1 ≤ w and ℓ_i ≤ w + 1 for 2 ≤ i ≤ m − 1; reason: same condition
--   - encoding: log (base two) and ln → `Real.logb 2` and `Real.log`; reason: the paper's convention (§2): logarithms are to base two, ln is natural
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 10 (PDF 12), Lemma 4.2; proof App. A.3.2, pp. 22–23 (PDF 24–25)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem lemma_4_2 (pb : Problem) (n m w : ℕ) (p0 ε : ℝ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hw1 : 1 ≤ w) (hwn : w ≤ n) (hp00 : 0 < p0) (hp01 : p0 < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (M : Fin (m - 1) → ℕ) (P0 : RandProtocol n m pb M)
    (hP0 : ∀ x, p0 ≤ P0.successProb x) (hshape : LengthShape M w) (u : ℕ)
    (hu : (if (partBound n w : ℝ) * p0 ≤ 1 then
            3 + 47 * Real.log (1 / ((partBound n w : ℝ) * p0)) +
              65 * Real.sqrt (partBound n w : ℝ) * Real.logb 2 (2 / ε)
          else 2 + 65 * Real.sqrt (partBound n w : ℝ) * Real.logb 2 (2 / ε)) ≤ (u : ℝ)) :
    ∃ (M' : Fin (m + u - 1) → ℕ) (P : RandProtocol n (m + u) pb M'),
      P.IsEpsError ε ∧ LengthShape M' w ∧ totalComm M' ≤ totalComm M + u * (w + 1) := by sorry

end ConservativePJ.ManyPlayers
