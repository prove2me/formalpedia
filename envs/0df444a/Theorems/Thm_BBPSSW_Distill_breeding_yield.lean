-- Prove2me | Theorems.Thm_BBPSSW_Distill_breeding_yield
-- name    : BBPSSW.Distill.breeding_yield
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:46:16.985635+00:00
-- url     : https://prove2.me/theorems/8d11b167-7598-47fd-83bf-604cddb73024
-- title:
--   Breeding: $n$ Bell-diagonal pairs plus $\lceil n(S(W)+\delta)\rceil$ pure $\Phi^+$ pairs yield $n$ near-perfect $\Phi^+$ pairs
-- statement:
--   Let $W$ be a Bell-diagonal two-spin state with von Neumann entropy $S(W)=-\mathrm{Tr}\,W\log_2W<1$. For all $\delta>0$ and $\varepsilon>0$ there is $N$ such that for every $n\ge N$, with $t=\lceil n(S(W)+\delta)\rceil$, some finite-round LOCC protocol $\Lambda$ maps
--
--   $$W^{\otimes n}\otimes(\Phi^+)^{\otimes t}$$
--
--   (the first $n$ pairs impure, the last $t$ perfect $\Phi^+$) to $n$ pairs with
--
--   $$\big\langle(\Phi^+)^{\otimes n}\big|\,\Lambda\big(W^{\otimes n}\otimes(\Phi^+)^{\otimes t}\big)\,\big|(\Phi^+)^{\otimes n}\big\rangle\ge1-\varepsilon .$$
--
--   The net gain is $n-t\approx n(1-S(W)-\delta)$ pure pairs: breeding has yield $1-S(W)$, positive when $S(W)<1$.
--
--   Differences from the source:
--   - reading: n·(S(W)+δ) prepurified Φ+ states; δ can approach 0 for large n → ⌈n(S(W)+δ)⌉ perfect Φ+ pairs, for every δ > 0 and all n ≥ N; reason: integer count of pairs; prepurified pairs taken perfect, as in B1's idealization
--   - reading: find all the errors with arbitrarily small chance of failure; yield 1−S(W) → output fidelity ≥ 1 − ε with (Φ+)^⊗n for every ε > 0, from n impure and t seed pairs; reason: the output of a protocol that succeeds with probability ≥ 1 − ε has fidelity ≥ 1 − ε; the net count n − t is the yield
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 3, steps B1–B3 and the two following paragraphs ("The breeding method has a yield 1−S(W)")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_IsBellDiagonal
import Definitions.Def_BBPSSW_Distill_pairsState
import Definitions.Def_BBPSSW_Distill_pairsVec

open QAlgorithms.Papers.Independent.Information100.P21 (QQ quad FiniteLOCC)
open ShadowTomography.QuantumLB (vnEntropy)

namespace BBPSSW.Distill

/-- **Breeding: `n` Bell-diagonal pairs and `n(S(W) + δ)` pure Φ⁺ pairs yield `n` pure Φ⁺ pairs.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 3, steps B1–B3 and the following paragraphs: "B1. Alice and Bob start with n impure
pairs described by any Bell-diagonal density matrix W with S(W) < 1, and n·(S(W)+δ) prepurified
Φ+ states … Here δ is a positive constant that can be allowed to approach 0 in the limit of
large n. … The number of BXOR tests per impure pair required to find all the errors, with
arbitrarily small chance of failure, approaches the entropy of the impure pairs,
S(W) = −TrW log2 W, in the limit of large n." and "The breeding method has a yield 1−S(W),
producing more pure pairs than consumed if the mixed state's von Neumann entropy, S(W), is less
than 1."

Let `W` be a Bell-diagonal two-qubit state with von Neumann entropy `S(W) < 1` (in bits). For
all `δ > 0` and `ε > 0` there is `N` such that for every `n ≥ N`, with `t = ⌈n (S(W) + δ)⌉`,
some finite-round LOCC protocol `Λ` maps the `n + t` pairs
`W^{⊗n} ⊗ (Φ⁺)^{⊗t}` (the first `n` pairs impure, the last `t` perfect Φ⁺) to `n` pairs whose
fidelity with `(Φ⁺)^{⊗n}` is at least `1 − ε`. The net gain `n − t ≈ n(1 − S(W) − δ)` is the
yield `1 − S(W)`.

**Formalization Note.** "With arbitrarily small chance of failure" is output fidelity
`≥ 1 − ε` for an arbitrary `ε > 0`; "δ can approach 0 in the limit of large n" is the
quantification over every `δ > 0` with `n` large. The prepurified pairs are taken perfect.
`vnEntropy` (`ShadowTomography.QuantumLB.vnEntropy`) is `−∑ λ log₂ λ` over the eigenvalues. -/
theorem breeding_yield (W : Matrix QQ QQ ℂ) (hW : IsBellDiagonal W) (hS : vnEntropy W < 1)
    (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℕ, t = ⌈(n : ℝ) * (vnEntropy W + δ)⌉₊ →
      ∃ Λ : QAlgorithms.Superop (Fin (2 ^ (n + t)) × Fin (2 ^ (n + t))) (Fin (2 ^ n) × Fin (2 ^ n)),
        FiniteLOCC Λ ∧
        1 - ε ≤ quad
          (Λ (pairsState fun j : Fin (n + t) =>
            if (j : ℕ) < n then W else QAlgorithms.pureDensity (bellVec .phiPlus)))
          (pairsVec fun _ : Fin n => bellVec .phiPlus) := by sorry

end BBPSSW.Distill
