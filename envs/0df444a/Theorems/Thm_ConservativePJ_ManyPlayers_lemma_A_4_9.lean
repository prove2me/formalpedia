-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_lemma_A_4_9
-- name    : ConservativePJ.ManyPlayers.lemma_A_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:52.296495+00:00
-- url     : https://prove2.me/theorems/e77ea404-aa6d-4762-9244-21667e1db582
-- title:
--   Lemma A.4.9 — removal of silent players under the hard distribution, and $\beta-\theta\le T\sqrt{\ln2/n}$
-- statement:
--   **Removal under the hard distribution.** Let $n\ge2$, $k\ge2$ and $0<\beta\le1$, and let $P$ be a deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_k$, or for $\mathrm{MPJ}_k$, with total communication $T$ and success probability at least $\beta$ under the hard distribution of its problem ($\mu$, resp. $\mu_{\mathrm{bool}}$). Let $\theta=1/n$ for $\widehat{\mathrm{MPJ}}_k$ and $\theta=1/2$ for $\mathrm{MPJ}_k$.
--
--   1. If $\beta>\theta$, there is a deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_{k'}$, or for $\mathrm{MPJ}_{k'}$ respectively, with $2\le k'\le T+1$ players and success probability at least $\beta$ under the hard distribution of its problem; its message alphabets are those of the players of $P$ who send at least one bit, so its total communication is $T$.
--   2. Whether or not $\beta>\theta$,
--   $$\beta-\frac1n\le T\sqrt{\frac{\ln2}n}\ \text{ for }\widehat{\mathrm{MPJ}}_k,\qquad \beta-\frac12\le T\sqrt{\frac{\ln2}n}\ \text{ for }\mathrm{MPJ}_k.\tag{31}$$
--
--   It supplies the $\sqrt n$ term of Corollary A.4.10.
--
--   Differences from the source:
--   - encoding: "The same holds with MPJ in place of MPĴ" (a separate sentence) → one statement quantified over `pb : Problem` (`.hat` = MPĴ, `.bool` = MPJ); reason: both cases at once; same content
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: last layer of MPJ_k maps into {0, 1} → `Bool`; reason: relabelling
--   - encoding: "the hard distribution of its problem"; θ → `hardSuccess pb P` (= `successMu` for `.hat`, `successMuBool` for `.bool`); `theta n pb` (= 1/n, 1/2); reason: the two cases of the lemma in one statement; (31) is β − θ ≤ T√(ln 2/n)
--   - encoding: "Its message alphabets are those of the players of P who send at least one bit" → a strictly increasing `e` onto the players with ℓ_i ≥ 1, and M′_i = M_{e(i)}; reason: same alphabets in the same order
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 45 (PDF 47), Lemma A.4.9 (App. A.4.8); θ defined p. 44 (PDF 46); proof pp. 45–46 (PDF 47–48)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem lemma_A_4_9 (pb : Problem) (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (M : Fin (k - 1) → ℕ) (P : DetProtocol n k pb M)
    (hsucc : β ≤ hardSuccess pb P) :
    (theta n pb < β →
      ∃ k' : ℕ, 2 ≤ k' ∧ k' ≤ totalComm M + 1 ∧
        ∃ (M' : Fin (k' - 1) → ℕ) (P' : DetProtocol n k' pb M'),
          β ≤ hardSuccess pb P' ∧
          (∃ e : Fin (k' - 1) → Fin (k - 1), StrictMono e ∧
            Set.range e = {i : Fin (k - 1) | 1 ≤ msgLength (M i)} ∧ ∀ i, M' i = M (e i)) ∧
          totalComm M' = totalComm M) ∧
    β - theta n pb ≤ (totalComm M : ℝ) * Real.sqrt (Real.log 2 / (n : ℝ)) := by sorry

end ConservativePJ.ManyPlayers
