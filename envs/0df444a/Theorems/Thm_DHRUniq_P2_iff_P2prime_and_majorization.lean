-- Prove2me | Theorems.Thm_DHRUniq_P2_iff_P2prime_and_majorization
-- name    : DHRUniq.P2_iff_P2prime_and_majorization
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:38.710192+00:00
-- url     : https://prove2.me/theorems/076c9937-07aa-4679-90a7-7bb32bec7b50
-- title:
--   §5.2, p. 10: (P2) is equivalent to (P2′) and monotonicity under majorization
-- statement:
--   Let $E$ be a functional on pure states. Then $E$ satisfies (P2) if and only if it satisfies (P2′) and, for all pure states $\varrho$ and $\sigma$,
--
--   $$
--   \text{the Schmidt coefficients of }\varrho\text{ majorize those of }\sigma\quad\Longrightarrow\quad E(\varrho)\le E(\sigma).
--   $$
--
--   This turns LQCC monotonicity, a statement about all protocols, into a statement about the Schmidt coefficients alone.
--
--   Differences from the source:
--   - encoding: E is a functional on pure states → E is a real function on all matrices over finite bipartite index types; reason: only its values at |ψ⟩⟨ψ| for unit ψ are read, and every functional on pure states extends to such a function
--   - encoding: finite-dimensional Hilbert spaces H^A, H^B → ℂ^a, ℂ^b for finite index types a, b with the standard basis; reason: every finite-dimensional Hilbert space is unitarily isomorphic to such a space
--   - reading: ϱ and σ, spaces not specified → ϱ and σ may live on different local spaces; reason: (P2′) compares states across spaces (p. 18: "Using (P2′), we may assume that H^A ≡ H^B ≡ H"), and this is the wider reading
--   - encoding: Schmidt coefficients of ϱ majorize those of σ → Majorizes on the decreasing lists of non-zero coefficients, compared up to the shorter length; reason: this is Definition 6, for sequences of different lengths
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, p. 10, the sentence after (P2′)

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_Majorizes
import Definitions.Def_DHRUniq_schmidtCoeffs
import Definitions.Def_DHRUniq_P2
import Definitions.Def_DHRUniq_P2prime
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)

namespace DHRUniq

/-- **§5.2, p. 10, the sentence after (P2′)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2): "By Nielsen's theorem and the proof of Lemma 9
below, (P2) is equivalent to assuming (P2′) and that if the Schmidt coefficients of `ϱ` majorize those
of `σ` then `E(ϱ) ≤ E(σ)`."

**Formalization Note** `ϱ = P_ψ` and `σ = P_φ` may live on different local spaces, as in (P2′). The
Schmidt coefficients are the non-zero ones, decreasing; Definition 6 compares lists of different
lengths up to the shorter length. -/
theorem P2_iff_P2prime_and_majorization (E : BipartiteFunctional) :
    P2 E ↔ P2prime E ∧
      ∀ ⦃a b a' b' : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
        [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
        (ψ : a × b → ℂ) (φ : a' × b' → ℂ), IsUnitVec ψ → IsUnitVec φ →
        Majorizes (schmidtCoeffs ψ) (schmidtCoeffs φ) → E (pureState ψ) ≤ E (pureState φ) := by sorry

end DHRUniq
