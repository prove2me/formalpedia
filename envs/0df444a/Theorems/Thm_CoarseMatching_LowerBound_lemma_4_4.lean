-- Prove2me | Theorems.Thm_CoarseMatching_LowerBound_lemma_4_4
-- name    : CoarseMatching.LowerBound.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:32.481206+00:00
-- url     : https://prove2.me/theorems/237c6f98-dfcc-4c08-a7c7-2936e82ac3e3
-- title:
--   Lemma 4.4 — Resource-preserving Hidden-Core reduction
-- statement:
--   For every integer $t\ge2$ there is $C_t>0$, uniform over integers $a\ge2$ and positive multiples $m$ of $a2^{t-1}$. There are positive integers $d\le h$ and normalized laws $P_0,P_1$ on $\{0,\ldots,d\}$ such that
--
--   $$h\le C_tam,\qquad P_0(Z>0)\le1/a,\qquad P_1(Z>0)=1.$$
--
--   For every universe $U$ with $|U|\ge ah$, a Hidden-Core protocol with communicated transcript-determined output gives a protocol for $t$-fold Unique Disjointness with the same alternating-message count and entrywise length bounds, and
--
--   $$\mathrm{gap}(\tau)\ge2^{1-t}\mathrm{gap}(\pi).$$
--
--   The choices of sizes and laws precede the universe and the protocol. The resource interface covers both fixed and variable message counts and preserves the starting sender. This is the source’s communication reduction.
--
--   Differences from the source:
--   - encoding: h=O_t(am) → ∀t≥2, ∃C_t>0 before a,m,U and π, with h≤C_tam; reason: the constant depends only on t
--   - encoding: protocols whose separate local input sizes are fixed → total strategies on all finite subsets with resource bounds on the size and promise domain; reason: invalid local inputs can be replaced by fixed valid local sets without communication; no valid input or resource guarantee is lost
--   - encoding: same rounds and same message-length bounds including the output → preservation of total, entrywise and alternating-round resource predicates, with an actually sent final output bit; reason: binary transcripts charge every transmitted bit and admit no free length or stopping signal
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), Lemma 4.4, printed p. 14 (PDF p. 15). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_UniqueDisjointness
import Definitions.Def_CoarseMatching_LowerBound_HiddenCore

namespace CoarseMatching.LowerBound

/-- Gillat Kol, STOC 2027 submission #1135 (October 2026), Lemma 4.4,
printed p.14 / PDF p.15. Uniform size constant depends only on t.
The divisibility is by a*2^(t-1), not a^(2t-1).
All message and round bounds and the communicated output are preserved. -/
theorem lemma_4_4 : ∀ t : ℕ, 2 ≤ t → ∃ C : ℝ, 0 < C ∧
    ∀ a m : ℕ, 2 ≤ a → 1 ≤ m → a*2^(t-1) ∣ m →
      ∃ (d h : ℕ) (P₀ P₁ : CountLaw d),
        1 ≤ d ∧ d ≤ h ∧ (h : ℝ) ≤ C*(a : ℝ)*(m : ℝ) ∧
        EquationFour (a : ℝ) P₀ P₁ ∧
        ∀ (U : Type) [Fintype U] [DecidableEq U], a*h ≤ Fintype.card U →
          ∀ π : Protocol (Finset U) (Finset U),
            π.TranscriptDetermined → OutputSentOn (HiddenInputs h d) π →
            ∃ τ : Protocol (UDInput m t) (UDInput m t),
              τ.TranscriptDetermined ∧ OutputSentOn (UDInputs m t) τ ∧
              Preserves (HiddenInputs h d) (UDInputs m t) π τ ∧
              (2 : ℝ)^(1-(t : ℝ))*hiddenGap h d P₀ P₁ π ≤ udGap m t τ := by sorry

end CoarseMatching.LowerBound
